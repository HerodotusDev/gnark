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
	"github.com/fxamacker/cbor/v2"
	"io"
	"reflect"
	"runtime"
	"sync"
	"time"

	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/internal/backend/ioutils"
	"github.com/consensys/gnark/logger"
	"github.com/consensys/gnark/profile"

	"github.com/consensys/gnark-crypto/ecc"
	"math"

	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

// R1CS describes a set of R1CS constraint
type R1CS struct {
	constraint.R1CSCore
	CoeffTable
	arithEngine
}

// NewR1CS returns a new R1CS and sets cs.Coefficient (fr.Element) from provided big.Int values
//
// capacity pre-allocates memory for capacity nbConstraints
func NewR1CS(capacity int) *R1CS {
	r := R1CS{
		R1CSCore: constraint.R1CSCore{
			System:      constraint.NewSystem(fr.Modulus()),
			Constraints: make([]constraint.R1C, 0, capacity),
		},
		CoeffTable: newCoeffTable(capacity / 10),
	}
	return &r
}

func (cs *R1CS) AddConstraint(r1c constraint.R1C, debugInfo ...constraint.DebugInfo) int {
	profile.RecordConstraint()
	cs.Constraints = append(cs.Constraints, r1c)
	cID := len(cs.Constraints) - 1
	if len(debugInfo) == 1 {
		cs.DebugInfo = append(cs.DebugInfo, constraint.LogEntry(debugInfo[0]))
		cs.MDebug[cID] = len(cs.DebugInfo) - 1
	}

	cs.UpdateLevel(cID, &r1c)

	return cID
}

// Solve returns the vector w solution to the system, that is
// Aw o Bw - Cw = 0
func (cs *R1CS) Solve(witness witness.Witness, opts ...solver.Option) (any, error) {
	opt, err := solver.NewConfig(opts...)
	if err != nil {
		return nil, err
	}

	var res R1CSSolution

	s := ecc.NextPowerOfTwo(uint64(len(cs.Constraints)))
	res.A = make(fr.Vector, len(cs.Constraints), s)
	res.B = make(fr.Vector, len(cs.Constraints), s)
	res.C = make(fr.Vector, len(cs.Constraints), s)

	v := witness.Vector().(fr.Vector)

	res.W, err = cs.solve(v, res.A, res.B, res.C, opt)
	if err != nil {
		return nil, err
	}

	return &res, nil
}

// Solve sets all the wires and returns the a, b, c vectors.
// the cs system should have been compiled before. The entries in a, b, c are in Montgomery form.
// a, b, c vectors: ab-c = hz
// witness = [publicWires | secretWires] (without the ONE_WIRE !)
// returns  [publicWires | secretWires | internalWires ]
func (cs *R1CS) solve(witness, a, b, c fr.Vector, opt solver.Config) (fr.Vector, error) {
	log := logger.Logger().With().Int("nbConstraints", len(cs.Constraints)).Str("backend", "groth16").Logger()

	nbWires := len(cs.Public) + len(cs.Secret) + cs.NbInternalVariables
	solution, err := newSolution(nbWires, opt.HintFunctions, cs.MHintsDependencies, cs.MHints, cs.Coefficients, &cs.System.SymbolTable)
	if err != nil {
		return make(fr.Vector, nbWires), err
	}
	start := time.Now()

	if len(witness) != len(cs.Public)-1+len(cs.Secret) { // - 1 for ONE_WIRE
		err = fmt.Errorf("invalid witness size, got %d, expected %d = %d (public) + %d (secret)", len(witness), int(len(cs.Public)-1+len(cs.Secret)), len(cs.Public)-1, len(cs.Secret))
		log.Err(err).Send()
		return solution.values, err
	}

	// compute the wires and the a, b, c polynomials
	if len(a) != len(cs.Constraints) || len(b) != len(cs.Constraints) || len(c) != len(cs.Constraints) {
		err = errors.New("invalid input size: len(a, b, c) == len(Constraints)")
		log.Err(err).Send()
		return solution.values, err
	}

	solution.solved[0] = true // ONE_WIRE
	solution.values[0].SetOne()
	copy(solution.values[1:], witness)
	for i := range witness {
		solution.solved[i+1] = true
	}

	// keep track of the number of wire instantiations we do, for a sanity check to ensure
	// we instantiated all wires
	solution.nbSolved += uint64(len(witness) + 1)

	// now that we know all inputs are set, defer log printing once all solution.values are computed
	// (or sooner, if a constraint is not satisfied)
	defer solution.printLogs(opt.Logger, cs.Logs)

	if err := cs.parallelSolve(a, b, c, &solution); err != nil {
		if unsatisfiedErr, ok := err.(*UnsatisfiedConstraintError); ok {
			log.Err(errors.New("unsatisfied constraint")).Int("id", unsatisfiedErr.CID).Send()
		} else {
			log.Err(err).Send()
		}
		return solution.values, err
	}

	// sanity check; ensure all wires are marked as "instantiated"
	if !solution.isValid() {
		log.Err(errors.New("solver didn't instantiate all wires")).Send()
		panic("solver didn't instantiate all wires")
	}

	log.Debug().Dur("took", time.Since(start)).Msg("constraint system solver done")

	return solution.values, nil
}

func (cs *R1CS) parallelSolve(a, b, c fr.Vector, solution *solution) error {
	// minWorkPerCPU is the minimum target number of constraint a task should hold
	// in other words, if a level has less than minWorkPerCPU, it will not be parallelized and executed
	// sequentially without sync.
	const minWorkPerCPU = 50.0

	// cs.Levels has a list of levels, where all constraints in a level l(n) are independent
	// and may only have dependencies on previous levels
	// for each constraint
	// we are guaranteed that each R1C contains at most one unsolved wire
	// first we solve the unsolved wire (if any)
	// then we check that the constraint is valid
	// if a[i] * b[i] != c[i]; it means the constraint is not satisfied

	var wg sync.WaitGroup
	chTasks := make(chan []int, runtime.NumCPU())
	chError := make(chan *UnsatisfiedConstraintError, runtime.NumCPU())

	// start a worker pool
	// each worker wait on chTasks
	// a task is a slice of constraint indexes to be solved
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for t := range chTasks {
				for _, i := range t {
					// for each constraint in the task, solve it.
					if err := cs.solveConstraint(cs.Constraints[i], solution, &a[i], &b[i], &c[i]); err != nil {
						var debugInfo *string
						if dID, ok := cs.MDebug[i]; ok {
							debugInfo = new(string)
							*debugInfo = solution.logValue(cs.DebugInfo[dID])
						}
						chError <- &UnsatisfiedConstraintError{CID: i, Err: err, DebugInfo: debugInfo}
						wg.Done()
						return
					}
				}
				wg.Done()
			}
		}()
	}

	// clean up pool go routines
	defer func() {
		close(chTasks)
		close(chError)
	}()

	// for each level, we push the tasks
	for _, level := range cs.Levels {

		// max CPU to use
		maxCPU := float64(len(level)) / minWorkPerCPU

		if maxCPU <= 1.0 {
			// we do it sequentially
			for _, i := range level {
				if err := cs.solveConstraint(cs.Constraints[i], solution, &a[i], &b[i], &c[i]); err != nil {
					var debugInfo *string
					if dID, ok := cs.MDebug[i]; ok {
						debugInfo = new(string)
						*debugInfo = solution.logValue(cs.DebugInfo[dID])
					}
					return &UnsatisfiedConstraintError{CID: i, Err: err, DebugInfo: debugInfo}
				}
			}
			continue
		}

		// number of tasks for this level is set to number of CPU
		// but if we don't have enough work for all our CPU, it can be lower.
		nbTasks := runtime.NumCPU()
		maxTasks := int(math.Ceil(maxCPU))
		if nbTasks > maxTasks {
			nbTasks = maxTasks
		}
		nbIterationsPerCpus := len(level) / nbTasks

		// more CPUs than tasks: a CPU will work on exactly one iteration
		// note: this depends on minWorkPerCPU constant
		if nbIterationsPerCpus < 1 {
			nbIterationsPerCpus = 1
			nbTasks = len(level)
		}

		extraTasks := len(level) - (nbTasks * nbIterationsPerCpus)
		extraTasksOffset := 0

		for i := 0; i < nbTasks; i++ {
			wg.Add(1)
			_start := i*nbIterationsPerCpus + extraTasksOffset
			_end := _start + nbIterationsPerCpus
			if extraTasks > 0 {
				_end++
				extraTasks--
				extraTasksOffset++
			}
			// since we're never pushing more than num CPU tasks
			// we will never be blocked here
			chTasks <- level[_start:_end]
		}

		// wait for the level to be done
		wg.Wait()

		if len(chError) > 0 {
			return <-chError
		}
	}

	return nil
}

// IsSolved
// Deprecated: use _, err := Solve(...) instead
func (cs *R1CS) IsSolved(witness witness.Witness, opts ...solver.Option) error {
	_, err := cs.Solve(witness, opts...)
	return err
}

// divByCoeff sets res = res / t.Coeff
func (cs *R1CS) divByCoeff(res *fr.Element, t constraint.Term) {
	cID := t.CoeffID()
	switch cID {
	case constraint.CoeffIdOne:
		return
	case constraint.CoeffIdMinusOne:
		res.Neg(res)
	case constraint.CoeffIdZero:
		panic("division by 0")
	default:
		// this is slow, but shouldn't happen as divByCoeff is called to
		// remove the coeff of an unsolved wire
		// but unsolved wires are (in gnark frontend) systematically set with a coeff == 1 or -1
		res.Div(res, &cs.Coefficients[cID])
	}
}

// solveConstraint compute unsolved wires in the constraint, if any and set the solution accordingly
//
// returns an error if the solver called a hint function that errored
// returns false, nil if there was no wire to solve
// returns true, nil if exactly one wire was solved. In that case, it is redundant to check that
// the constraint is satisfied later.
func (cs *R1CS) solveConstraint(r constraint.R1C, solution *solution, a, b, c *fr.Element) error {

	// the index of the non-zero entry shows if L, R or O has an uninstantiated wire
	// the content is the ID of the wire non instantiated
	var loc uint8

	var termToCompute constraint.Term

	processLExp := func(l constraint.LinearExpression, val *fr.Element, locValue uint8) error {
		for _, t := range l {
			vID := t.WireID()

			// wire is already computed, we just accumulate in val
			if solution.solved[vID] {
				solution.accumulateInto(t, val)
				continue
			}

			// first we check if this is a hint wire
			if hint, ok := cs.MHints[vID]; ok {
				if err := solution.solveWithHint(vID, hint); err != nil {
					return err
				}
				// now that the wire is saved, accumulate it into a, b or c
				solution.accumulateInto(t, val)
				continue
			}

			if loc != 0 {
				panic("found more than one wire to instantiate")
			}
			termToCompute = t
			loc = locValue
		}
		return nil
	}

	if err := processLExp(r.L, a, 1); err != nil {
		return err
	}

	if err := processLExp(r.R, b, 2); err != nil {
		return err
	}

	if err := processLExp(r.O, c, 3); err != nil {
		return err
	}

	if loc == 0 {
		// there is nothing to solve, may happen if we have an assertion
		// (ie a constraints that doesn't yield any output)
		// or if we solved the unsolved wires with hint functions
		var check fr.Element
		if !check.Mul(a, b).Equal(c) {
			return fmt.Errorf("%s ⋅ %s != %s", a.String(), b.String(), c.String())
		}
		return nil
	}

	// we compute the wire value and instantiate it
	wID := termToCompute.WireID()

	// solver result
	var wire fr.Element

	switch loc {
	case 1:
		if !b.IsZero() {
			wire.Div(c, b).
				Sub(&wire, a)
			a.Add(a, &wire)
		} else {
			// we didn't actually ensure that a * b == c
			var check fr.Element
			if !check.Mul(a, b).Equal(c) {
				return fmt.Errorf("%s ⋅ %s != %s", a.String(), b.String(), c.String())
			}
		}
	case 2:
		if !a.IsZero() {
			wire.Div(c, a).
				Sub(&wire, b)
			b.Add(b, &wire)
		} else {
			var check fr.Element
			if !check.Mul(a, b).Equal(c) {
				return fmt.Errorf("%s ⋅ %s != %s", a.String(), b.String(), c.String())
			}
		}
	case 3:
		wire.Mul(a, b).
			Sub(&wire, c)

		c.Add(c, &wire)
	}

	// wire is the term (coeff * value)
	// but in the solution we want to store the value only
	// note that in gnark frontend, coeff here is always 1 or -1
	cs.divByCoeff(&wire, termToCompute)
	solution.set(wID, wire)

	return nil
}

// GetConstraints return the list of R1C and a coefficient resolver
func (cs *R1CS) GetConstraints() ([]constraint.R1C, constraint.Resolver) {
	return cs.Constraints, cs
}

// GetNbCoefficients return the number of unique coefficients needed in the R1CS
func (cs *R1CS) GetNbCoefficients() int {
	return len(cs.Coefficients)
}

// CurveID returns curve ID as defined in gnark-crypto
func (cs *R1CS) CurveID() ecc.ID {
	return ecc.BLS12_381
}

// WriteTo encodes R1CS into provided io.Writer using cbor
func (cs *R1CS) WriteTo(w io.Writer) (int64, error) {
	_w := ioutils.WriterCounter{W: w} // wraps writer to count the bytes written
	enc, err := cbor.CoreDetEncOptions().EncMode()
	if err != nil {
		return 0, err
	}
	encoder := enc.NewEncoder(&_w)

	// encode our object
	err = encoder.Encode(cs)
	return _w.N, err
}

// ReadFrom attempts to decode R1CS from io.Reader using cbor
func (cs *R1CS) ReadFrom(r io.Reader) (int64, error) {
	dm, err := cbor.DecOptions{
		MaxArrayElements: 134217728,
		MaxMapPairs:      134217728,
	}.DecMode()

	if err != nil {
		return 0, err
	}
	decoder := dm.NewDecoder(r)

	// initialize coeff table
	cs.CoeffTable = newCoeffTable(0)

	if err := decoder.Decode(&cs); err != nil {
		return int64(decoder.NumBytesRead()), err
	}

	if err := cs.CheckSerializationHeader(); err != nil {
		return int64(decoder.NumBytesRead()), err
	}

	return int64(decoder.NumBytesRead()), nil
}

func (cs *R1CS) Equal(o constraint.ConstraintSystem) bool {
	O, ok := o.(*R1CS)
	return ok &&
		reflect.DeepEqual(cs.CoeffTable, O.CoeffTable) &&
		reflect.DeepEqual(cs.Constraints, O.Constraints) &&
		cs.System.Equal(&O.System)
}
