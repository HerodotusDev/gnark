package constraint

func (cs *System) GetCallData(instruction Instruction) []uint32 {
	blueprint := cs.Blueprints[instruction.BlueprintID]
	nbInputs := blueprint.NbInputs()
	if nbInputs < 0 {
		// happens with R1C of unknown size or hints
		nbInputs = int(cs.CallData[instruction.StartCallData])
	}
	return cs.CallData[instruction.StartCallData : instruction.StartCallData+uint64(nbInputs)]
}

type Instruction struct {
	BlueprintID      BlueprintID
	ConstraintOffset uint32 // might not be strictly necessary; but speeds up solver.
	StartCallData    uint64 // call data slice (end can be returned by Blueprint)
}

func (cs *System) AddConstraint(c R1C, bID BlueprintID) int {
	instruction := cs.compressR1C(&c, bID)
	cs.Instructions = append(cs.Instructions, instruction)

	cs.updateLevel(len(cs.Instructions)-1, &c)

	return cs.NbConstraints - 1
}

func (cs *System) AddSparseR1C(c SparseR1C, bID BlueprintID) int {
	instruction := cs.compressSparseR1C(&c, bID)
	cs.Instructions = append(cs.Instructions, instruction)

	cs.updateLevel(len(cs.Instructions)-1, &c)

	return cs.NbConstraints - 1
}

func (cs *System) compressSparseR1C(c *SparseR1C, bID BlueprintID) Instruction {
	inst := Instruction{
		StartCallData:    uint64(len(cs.CallData)),
		ConstraintOffset: uint32(cs.NbConstraints),
		BlueprintID:      bID,
	}
	blueprint := cs.Blueprints[bID]
	calldata := blueprint.(BlueprintSparseR1C).CompressSparseR1C(c)
	cs.CallData = append(cs.CallData, calldata...)
	cs.NbConstraints += blueprint.NbConstraints()
	return inst
}

func (cs *System) compressR1C(c *R1C, bID BlueprintID) Instruction {
	inst := Instruction{
		StartCallData:    uint64(len(cs.CallData)),
		ConstraintOffset: uint32(cs.NbConstraints),
		BlueprintID:      bID,
	}
	blueprint := cs.Blueprints[bID]
	calldata := blueprint.(BlueprintR1C).CompressR1C(c)
	cs.CallData = append(cs.CallData, calldata...)
	cs.NbConstraints += blueprint.NbConstraints()
	return inst
}

func (cs *System) compressHint(hm HintMapping, bID BlueprintID) Instruction {
	inst := Instruction{
		StartCallData:    uint64(len(cs.CallData)),
		ConstraintOffset: uint32(cs.NbConstraints), // unused.
		BlueprintID:      bID,
	}
	blueprint := cs.Blueprints[bID]
	calldata := blueprint.(BlueprintHint).CompressHint(hm)
	cs.CallData = append(cs.CallData, calldata...)
	return inst
}

// GetNbConstraints returns the number of constraints
func (cs *System) GetNbConstraints() int {
	return cs.NbConstraints
}

func (cs *System) CheckUnconstrainedWires() error {
	// TODO @gbotrel
	return nil
}