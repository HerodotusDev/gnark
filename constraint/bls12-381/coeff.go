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
	"github.com/consensys/gnark/constraint"

	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

// CoeffTable ensure we store unique coefficients in the constraint system
type CoeffTable struct {
	Coefficients []fr.Element
	mCoeffs      map[fr.Element]uint32 // maps coefficient to coeffID
}

func newCoeffTable(capacity int) CoeffTable {
	r := CoeffTable{
		Coefficients: make([]fr.Element, 5, 5+capacity),
		mCoeffs:      make(map[fr.Element]uint32, capacity),
	}

	r.Coefficients[constraint.CoeffIdZero].SetUint64(0)
	r.Coefficients[constraint.CoeffIdOne].SetOne()
	r.Coefficients[constraint.CoeffIdTwo].SetUint64(2)
	r.Coefficients[constraint.CoeffIdMinusOne].SetInt64(-1)
	r.Coefficients[constraint.CoeffIdMinusTwo].SetInt64(-2)

	return r

}

func (ct *CoeffTable) AddCoeff(coeff constraint.Element) uint32 {
	c := (*fr.Element)(coeff[:])
	var cID uint32
	if c.IsZero() {
		cID = constraint.CoeffIdZero
	} else if c.IsOne() {
		cID = constraint.CoeffIdOne
	} else if c.Equal(&two) {
		cID = constraint.CoeffIdTwo
	} else if c.Equal(&minusOne) {
		cID = constraint.CoeffIdMinusOne
	} else if c.Equal(&minusTwo) {
		cID = constraint.CoeffIdMinusTwo
	} else {
		cc := *c
		if id, ok := ct.mCoeffs[cc]; ok {
			cID = id
		} else {
			cID = uint32(len(ct.Coefficients))
			ct.Coefficients = append(ct.Coefficients, cc)
			ct.mCoeffs[cc] = cID
		}
	}
	return cID
}

func (ct *CoeffTable) MakeTerm(coeff *constraint.Element, variableID int) constraint.Term {
	cID := ct.AddCoeff(*coeff)
	return constraint.Term{VID: uint32(variableID), CID: cID}
}

// CoeffToString implements constraint.Resolver
func (ct *CoeffTable) CoeffToString(cID int) string {
	return ct.Coefficients[cID].String()
}
