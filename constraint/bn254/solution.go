// Copyright 2020 ConsenSys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by gnark DO NOT EDIT

package cs

import (
	"errors"
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/field/pool"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/debug"
	"github.com/consensys/gnark/internal/utils"
	"github.com/rs/zerolog"
	"io"
	"math/big"
	"strconv"
	"strings"
	"sync/atomic"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// solution represent the state of the Solver during a call to System.Solve(...)
type solution struct {
	arithEngine

	cs *constraint.System
	st *debug.SymbolTable

	// values, coefficients and solved are index by the wire (variable) id
	values, coefficients []fr.Element
	solved               []bool
	nbSolved             uint64

	// maps hintID to hint function
	mHintsFunctions map[solver.HintID]solver.Hint

	a, b, c            fr.Vector // R1CS solver will compute the a,b,c matrices
	coefficientsNegInv fr.Vector // TODO @gbotrel this should be computed once SparseR1CS solver perf.
}

func newSolution(cs *constraint.System, nbWires int, hintFunctions map[solver.HintID]solver.Hint, coefficients []fr.Element, isR1CS bool) (solution, error) {

	s := solution{
		cs:              cs,
		st:              &cs.SymbolTable,
		values:          make([]fr.Element, nbWires),
		coefficients:    coefficients,
		solved:          make([]bool, nbWires),
		mHintsFunctions: hintFunctions,
	}

	// hintsDependencies is from compile time; it contains the list of hints the solver **needs**
	var missing []string
	for hintUUID, hintID := range cs.MHintsDependencies {
		if _, ok := s.mHintsFunctions[hintUUID]; !ok {
			missing = append(missing, hintID)
		}
	}

	if len(missing) > 0 {
		return s, fmt.Errorf("solver missing hint(s): %v", missing)
	}

	if isR1CS {
		n := ecc.NextPowerOfTwo(uint64(cs.GetNbConstraints()))
		s.a = make(fr.Vector, cs.GetNbConstraints(), n)
		s.b = make(fr.Vector, cs.GetNbConstraints(), n)
		s.c = make(fr.Vector, cs.GetNbConstraints(), n)
	} else {
		// TODO @gbotrel this could be done once in the CS, most of the time.
		s.coefficientsNegInv = fr.Vector(fr.BatchInvert(coefficients))
		for i := 0; i < len(s.coefficientsNegInv); i++ {
			s.coefficientsNegInv[i].Neg(&s.coefficientsNegInv[i])
		}
	}

	return s, nil
}

func (s *solution) set(id int, value fr.Element) {
	if s.solved[id] {
		panic("solving the same wire twice should never happen.")
	}
	s.values[id] = value
	s.solved[id] = true
	atomic.AddUint64(&s.nbSolved, 1)
}

// isValid returns true if all wires are solved
func (s *solution) isValid() bool {
	return int(s.nbSolved) == len(s.values)
}

// computeTerm computes coeff*variable
// TODO @gbotrel check if t is a Constant only
func (s *solution) computeTerm(t constraint.Term) fr.Element {
	cID, vID := t.CoeffID(), t.WireID()
	if cID != 0 && !s.solved[vID] {
		panic("computing a term with an unsolved wire")
	}
	switch cID {
	case constraint.CoeffIdZero:
		return fr.Element{}
	case constraint.CoeffIdOne:
		return s.values[vID]
	case constraint.CoeffIdTwo:
		var res fr.Element
		res.Double(&s.values[vID])
		return res
	case constraint.CoeffIdMinusOne:
		var res fr.Element
		res.Neg(&s.values[vID])
		return res
	default:
		var res fr.Element
		res.Mul(&s.coefficients[cID], &s.values[vID])
		return res
	}
}

// r += (t.coeff*t.value)
// TODO @gbotrel check t.IsConstant on the caller side when necessary
func (s *solution) accumulateInto(t constraint.Term, r *fr.Element) {
	cID := t.CoeffID()
	vID := t.WireID()

	switch cID {
	case constraint.CoeffIdZero:
		return
	case constraint.CoeffIdOne:
		r.Add(r, &s.values[vID])
	case constraint.CoeffIdTwo:
		var res fr.Element
		res.Double(&s.values[vID])
		r.Add(r, &res)
	case constraint.CoeffIdMinusOne:
		r.Sub(r, &s.values[vID])
	default:
		var res fr.Element
		res.Mul(&s.coefficients[cID], &s.values[vID])
		r.Add(r, &res)
	}
}

// solveWithHint executes a hint and assign the result to its defined outputs.
func (s *solution) solveWithHint(h constraint.HintMapping) error {
	// ensure hint function was provided
	f, ok := s.mHintsFunctions[h.HintID]
	if !ok {
		return errors.New("missing hint function")
	}

	// tmp IO big int memory
	nbInputs := len(h.Inputs)
	nbOutputs := len(h.Outputs)
	inputs := make([]*big.Int, nbInputs)
	outputs := make([]*big.Int, nbOutputs)
	for i := 0; i < nbOutputs; i++ {
		outputs[i] = pool.BigInt.Get()
		outputs[i].SetUint64(0)
	}

	q := fr.Modulus()

	for i := 0; i < nbInputs; i++ {
		var v fr.Element
		for _, term := range h.Inputs[i] {
			if term.IsConstant() {
				v.Add(&v, &s.coefficients[term.CoeffID()])
				continue
			}
			s.accumulateInto(term, &v)
		}
		inputs[i] = pool.BigInt.Get()
		v.BigInt(inputs[i])
	}

	err := f(q, inputs, outputs)

	var v fr.Element
	for i := range outputs {
		v.SetBigInt(outputs[i])
		s.set(h.Outputs[i], v)
		pool.BigInt.Put(outputs[i])
	}

	for i := range inputs {
		pool.BigInt.Put(inputs[i])
	}

	return err
}

func (s *solution) printLogs(log zerolog.Logger, logs []constraint.LogEntry) {
	if log.GetLevel() == zerolog.Disabled {
		return
	}

	for i := 0; i < len(logs); i++ {
		logLine := s.logValue(logs[i])
		log.Debug().Str(zerolog.CallerFieldName, logs[i].Caller).Msg(logLine)
	}
}

const unsolvedVariable = "<unsolved>"

func (s *solution) logValue(log constraint.LogEntry) string {
	var toResolve []interface{}
	var (
		eval         fr.Element
		missingValue bool
	)
	for j := 0; j < len(log.ToResolve); j++ {
		// before eval le

		missingValue = false
		eval.SetZero()

		for _, t := range log.ToResolve[j] {
			// for each term in the linear expression

			cID, vID := t.CoeffID(), t.WireID()
			if t.IsConstant() {
				// just add the constant
				eval.Add(&eval, &s.coefficients[cID])
				continue
			}

			if !s.solved[vID] {
				missingValue = true
				break // stop the loop we can't evaluate.
			}

			tv := s.computeTerm(t)
			eval.Add(&eval, &tv)
		}

		// after
		if missingValue {
			toResolve = append(toResolve, unsolvedVariable)
		} else {
			// we have to append our accumulator
			toResolve = append(toResolve, eval.String())
		}

	}
	if len(log.Stack) > 0 {
		var sbb strings.Builder
		for _, lID := range log.Stack {
			location := s.st.Locations[lID]
			function := s.st.Functions[location.FunctionID]

			sbb.WriteString(function.Name)
			sbb.WriteByte('\n')
			sbb.WriteByte('\t')
			sbb.WriteString(function.Filename)
			sbb.WriteByte(':')
			sbb.WriteString(strconv.Itoa(int(location.Line)))
			sbb.WriteByte('\n')
		}
		toResolve = append(toResolve, sbb.String())
	}
	return fmt.Sprintf(log.Format, toResolve...)
}

// Implement constraint.Solver
func (s *solution) GetValue(cID, vID uint32) constraint.Element {
	var r constraint.Element
	e := s.computeTerm(constraint.Term{CID: cID, VID: vID})
	copy(r[:], e[:])
	return r
}
func (s *solution) GetCoeff(cID uint32) constraint.Element {
	var r constraint.Element
	copy(r[:], s.coefficients[cID][:])
	return r
}
func (s *solution) SetValue(vID uint32, f constraint.Element) {
	s.set(int(vID), fr.Element(f[:]))
}

// UnsatisfiedConstraintError wraps an error with useful metadata on the unsatisfied constraint
type UnsatisfiedConstraintError struct {
	Err       error
	CID       int     // constraint ID
	DebugInfo *string // optional debug info
}

func (r *UnsatisfiedConstraintError) Error() string {
	if r.DebugInfo != nil {
		return fmt.Sprintf("constraint #%d is not satisfied: %s", r.CID, *r.DebugInfo)
	}
	return fmt.Sprintf("constraint #%d is not satisfied: %s", r.CID, r.Err.Error())
}

// R1CSSolution represent a valid assignment to all the variables in the constraint system.
// The vector W such that Aw o Bw - Cw = 0
type R1CSSolution struct {
	W       fr.Vector
	A, B, C fr.Vector
}

func (t *R1CSSolution) WriteTo(w io.Writer) (int64, error) {
	n, err := t.W.WriteTo(w)
	if err != nil {
		return n, err
	}
	a, err := t.A.WriteTo(w)
	n += a
	if err != nil {
		return n, err
	}
	a, err = t.B.WriteTo(w)
	n += a
	if err != nil {
		return n, err
	}
	a, err = t.C.WriteTo(w)
	n += a
	return n, err
}

func (t *R1CSSolution) ReadFrom(r io.Reader) (int64, error) {
	n, err := t.W.ReadFrom(r)
	if err != nil {
		return n, err
	}
	a, err := t.A.ReadFrom(r)
	a += n
	if err != nil {
		return n, err
	}
	a, err = t.B.ReadFrom(r)
	a += n
	if err != nil {
		return n, err
	}
	a, err = t.C.ReadFrom(r)
	n += a
	return n, err
}

// SparseR1CSSolution represent a valid assignment to all the variables in the constraint system.
type SparseR1CSSolution struct {
	L, R, O fr.Vector
}

func (t *SparseR1CSSolution) WriteTo(w io.Writer) (int64, error) {
	n, err := t.L.WriteTo(w)
	if err != nil {
		return n, err
	}
	a, err := t.R.WriteTo(w)
	n += a
	if err != nil {
		return n, err
	}
	a, err = t.O.WriteTo(w)
	n += a
	return n, err

}

func (t *SparseR1CSSolution) ReadFrom(r io.Reader) (int64, error) {
	n, err := t.L.ReadFrom(r)
	if err != nil {
		return n, err
	}
	a, err := t.R.ReadFrom(r)
	a += n
	if err != nil {
		return n, err
	}
	a, err = t.O.ReadFrom(r)
	a += n
	return n, err
}

// implements constraint.Field
type arithEngine struct{}

var _ constraint.Field = &arithEngine{}

var (
	two      fr.Element
	minusOne fr.Element
	minusTwo fr.Element
)

func init() {
	minusOne.SetOne()
	minusOne.Neg(&minusOne)
	two.SetOne()
	two.Double(&two)
	minusTwo.Neg(&two)
}

func (engine *arithEngine) FromInterface(i interface{}) constraint.Element {
	var e fr.Element
	if _, err := e.SetInterface(i); err != nil {
		// need to clean that --> some code path are dissimilar
		// for example setting a fr.Element from an fp.Element
		// fails with the above but succeeds through big int... (2-chains)
		b := utils.FromInterface(i)
		e.SetBigInt(&b)
	}
	var r constraint.Element
	copy(r[:], e[:])
	return r
}
func (engine *arithEngine) ToBigInt(c constraint.Element) *big.Int {
	e := (*fr.Element)(c[:])
	r := new(big.Int)
	e.BigInt(r)
	return r

}
func (engine *arithEngine) Mul(a, b constraint.Element) constraint.Element {
	_a := (*fr.Element)(a[:])
	_b := (*fr.Element)(b[:])
	_a.Mul(_a, _b)
	return a
}

func (engine *arithEngine) Add(a, b constraint.Element) constraint.Element {
	_a := (*fr.Element)(a[:])
	_b := (*fr.Element)(b[:])
	_a.Add(_a, _b)
	return a
}
func (engine *arithEngine) Sub(a, b constraint.Element) constraint.Element {
	_a := (*fr.Element)(a[:])
	_b := (*fr.Element)(b[:])
	_a.Sub(_a, _b)
	return a
}
func (engine *arithEngine) Neg(a constraint.Element) constraint.Element {
	e := (*fr.Element)(a[:])
	e.Neg(e)
	return a

}
func (engine *arithEngine) Inverse(a constraint.Element) constraint.Element {
	e := (*fr.Element)(a[:])
	e.Inverse(e)
	return a
}

func (engine *arithEngine) IsOne(a constraint.Element) bool {
	e := (*fr.Element)(a[:])
	return e.IsOne()
}

func (engine *arithEngine) One() constraint.Element {
	e := fr.One()
	var r constraint.Element
	copy(r[:], e[:])
	return r
}

func (engine *arithEngine) String(a constraint.Element) string {
	e := (*fr.Element)(a[:])
	return e.String()
}
