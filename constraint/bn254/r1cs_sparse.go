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
	"fmt"
	"github.com/consensys/gnark/constraint"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

type SparseR1CS = R1CS

// NewSparseR1CS returns a new SparseR1CS and sets r1cs.Coefficient (fr.Element) from provided big.Int values
func NewSparseR1CS(capacity int) *R1CS {
	cs := R1CS{
		System:     constraint.NewSystem(fr.Modulus(), capacity),
		CoeffTable: newCoeffTable(capacity / 10),
	}

	return &cs
}

// findUnsolvedWire computes wires associated with a hint function, if any
// if there is no remaining wire to solve, returns -1
// else returns the wire position (L -> 0, R -> 1, O -> 2)
func (cs *R1CS) findUnsolvedWire(c *constraint.SparseR1C, solution *solution) int {
	lID, rID, oID := c.L.WireID(), c.R.WireID(), c.O.WireID()

	if (c.L.CoeffID() != 0 || c.M[0].CoeffID() != 0) && !solution.solved[lID] {
		return 0
	}

	if (c.R.CoeffID() != 0 || c.M[1].CoeffID() != 0) && !solution.solved[rID] {
		return 1
	}

	if (c.O.CoeffID() != 0) && !solution.solved[oID] {
		return 2
	}
	return -1
}

// solveConstraint solve any unsolved wire in given constraint and update the solution
// a SparseR1C may have up to one unsolved wire (excluding hints)
// if it doesn't, then this function returns and does nothing
func (cs *R1CS) solveSparseR1C(c *constraint.SparseR1C, solution *solution, coefficientsNegInv fr.Vector) error {

	if c.Commitment == constraint.COMMITTED { // a constraint of the form f_L - PI_2 = 0 or f_L = Comm.
		return nil // these are there for enforcing the correctness of the commitment and can be skipped in solving time
	}

	lro := cs.findUnsolvedWire(c, solution)
	if lro == -1 {
		// no unsolved wire
		// can happen if the constraint contained only hint wires.
		return nil
	}
	if lro == 1 { // we solve for R: u1L+u2R+u3LR+u4O+k=0 => R(u2+u3L)+u1L+u4O+k = 0
		if !solution.solved[c.L.WireID()] {
			panic("L wire should be instantiated when we solve R")
		}
		var u1, u2, u3, den, num, v1, v2 fr.Element
		u3.Mul(&cs.Coefficients[c.M[0].CoeffID()], &cs.Coefficients[c.M[1].CoeffID()])
		u1.Set(&cs.Coefficients[c.L.CoeffID()])
		u2.Set(&cs.Coefficients[c.R.CoeffID()])
		den.Mul(&u3, &solution.values[c.L.WireID()]).Add(&den, &u2)

		v1 = solution.computeTerm(c.L)
		v2 = solution.computeTerm(c.O)
		num.Add(&v1, &v2).Add(&num, &cs.Coefficients[c.K])

		// TODO find a way to do lazy div (/ batch inversion)
		num.Div(&num, &den).Neg(&num)
		solution.set(c.L.WireID(), num)
		return nil
	}

	if lro == 0 { // we solve for L: u1L+u2R+u3LR+u4O+k=0 => L(u1+u3R)+u2R+u4O+k = 0
		if !solution.solved[c.R.WireID()] {
			panic("R wire should be instantiated when we solve L")
		}
		var u1, u2, u3, den, num, v1, v2 fr.Element
		u3.Mul(&cs.Coefficients[c.M[0].CoeffID()], &cs.Coefficients[c.M[1].CoeffID()])
		u1.Set(&cs.Coefficients[c.L.CoeffID()])
		u2.Set(&cs.Coefficients[c.R.CoeffID()])
		den.Mul(&u3, &solution.values[c.R.WireID()]).Add(&den, &u1)

		v1 = solution.computeTerm(c.R)
		v2 = solution.computeTerm(c.O)
		num.Add(&v1, &v2).Add(&num, &cs.Coefficients[c.K])

		// TODO find a way to do lazy div (/ batch inversion)
		num.Div(&num, &den).Neg(&num)
		solution.set(c.L.WireID(), num)
		return nil

	}
	// O we solve for O
	var o fr.Element
	cID, vID := c.O.CoeffID(), c.O.WireID()

	l := solution.computeTerm(c.L)
	r := solution.computeTerm(c.R)
	m0 := solution.computeTerm(c.M[0])
	m1 := solution.computeTerm(c.M[1])

	// o = - ((m0 * m1) + l + r + c.K) / c.O
	o.Mul(&m0, &m1).Add(&o, &l).Add(&o, &r).Add(&o, &cs.Coefficients[c.K])
	o.Mul(&o, &coefficientsNegInv[cID])

	solution.set(vID, o)

	return nil
}

// GetConstraints return the list of SparseR1C and a coefficient resolver
// TODO @gbotrel
func (cs *R1CS) GetConstraints2() ([]constraint.SparseR1C, constraint.Resolver) {

	toReturn := make([]constraint.SparseR1C, 0, cs.GetNbConstraints())

	for _, inst := range cs.Instructions {
		blueprint := cs.Blueprints[inst.BlueprintID]
		if bc, ok := blueprint.(constraint.BlueprintSparseR1C); ok {
			var sparseR1C constraint.SparseR1C
			calldata := cs.CallData[inst.StartCallData : inst.StartCallData+uint64(blueprint.NbInputs())]
			bc.DecompressSparseR1C(&sparseR1C, calldata)
			toReturn = append(toReturn, sparseR1C)
		} else {
			panic("not implemented")
		}
	}
	return toReturn, cs
}

func (cs *R1CS) GetCoefficient(i int) (r constraint.Coeff) {
	copy(r[:], cs.Coefficients[i][:])
	return
}

// checkConstraint verifies that the constraint holds
func (cs *R1CS) checkConstraint(c *constraint.SparseR1C, solution *solution) error {

	if c.Commitment != constraint.NOT { // a constraint of the form f_L - PI_2 = 0 or f_L = Comm.
		return nil // these are there for enforcing the correctness of the commitment and can be skipped in solving time
	}

	l := solution.computeTerm(c.L)
	r := solution.computeTerm(c.R)
	m0 := solution.computeTerm(c.M[0])
	m1 := solution.computeTerm(c.M[1])
	o := solution.computeTerm(c.O)

	// l + r + (m0 * m1) + o + c.K == 0
	var t fr.Element
	t.Mul(&m0, &m1).Add(&t, &l).Add(&t, &r).Add(&t, &o).Add(&t, &cs.Coefficients[c.K])
	if !t.IsZero() {
		return fmt.Errorf("qL⋅xa + qR⋅xb + qO⋅xc + qM⋅(xaxb) + qC != 0 → %s + %s + %s + (%s × %s) + %s != 0",
			l.String(),
			r.String(),
			o.String(),
			m0.String(),
			m1.String(),
			cs.Coefficients[c.K].String(),
		)
	}
	return nil

}
