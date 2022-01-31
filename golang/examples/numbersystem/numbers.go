package numbers

import (
	"log"

	modelator "github.com/informalsystems/modelator/golang"
)

// compile time check if steprunner interfaces are implemented
var (
	_ modelator.StepRunner = &NumberSystem{}
	_ modelator.StepI      = Step{}
)

// MaxNumber is the maximum bound for a and b
const MaxNumber uint64 = 6

// NumberSystem stores the system state
type NumberSystem struct {
	A    uint64
	B    uint64
	Sum  uint64
	Prod uint64
}

// Action is actions/events received by the system
type Action string

const (
	// None is no action
	None Action = "None"
	// IncreaseA is an action to increase A by 1
	IncreaseA = "IncreaseA"
	// IncreaseB is an action to increase B by 2
	IncreaseB = "IncreaseB"
)

// Step stores the transition data between states
type Step struct {
	A             uint64 `json:"a"`
	B             uint64 `json:"b"`
	Action        Action `json:"action"`
	ActionOutcome string `json:"actionOutcome"`
}

// NumberSystemError stores the errors from system
type NumberSystemError string

func (e NumberSystemError) Error() string {
	return string(e)
}

// Recalculate the system state
func (state *NumberSystem) Recalculate() {
	state.Sum = state.A + state.B
	state.Prod = state.A * state.B
}

// IncreaseA increases a and returns error if MaxNumber is reached
func (state *NumberSystem) IncreaseA(n uint64) error {
	if state.A+n <= MaxNumber {
		state.A += n
		state.Recalculate()
		return nil
	}
	return NumberSystemError("FAIL")
}

// IncreaseB increases b and returns error if MaxNumber is reached
func (state *NumberSystem) IncreaseB(n uint64) error {
	if state.B+n <= MaxNumber {
		state.B += n
		state.Recalculate()
		return nil
	}
	return NumberSystemError("FAIL")
}

// InitialStep initialize system state with initial values
func (state *NumberSystem) InitialStep(stepI modelator.StepI) error {
	step, ok := stepI.(Step)
	if !ok {
		return NumberSystemError("Failed to cast step interface to concrete step type")
	}
	state.A = step.A
	state.B = step.B
	state.Recalculate()
	return nil
}

// NextStep performs given step and modifies the current state
func (state *NumberSystem) NextStep(stepI modelator.StepI) error {
	step, ok := stepI.(Step)
	if !ok {
		return NumberSystemError("Failed to cast step interface to concrete step type")
	}
	var err error
	// Execute the action, and check the outcome
	switch step.Action {
	case None:
		err = nil
	case IncreaseA:
		err = state.IncreaseA(1)
	case IncreaseB:
		err = state.IncreaseB(2)
	default:
		log.Println(step.Action)
	}

	var outcome string

	if err != nil {
		outcome = string(err.(NumberSystemError))
	} else {
		outcome = "OK"
	}

	if outcome == step.ActionOutcome && state.A == step.A && state.B == step.B {
		return nil
	}

	return modelator.StepMismatch{
		Expected: step,
		Observed: state,
		Outcome:  outcome,
	}
}
