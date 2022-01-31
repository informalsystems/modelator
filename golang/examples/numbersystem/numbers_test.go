package numbers

import (
	"encoding/json"
	"fmt"
	"testing"

	modelator "github.com/informalsystems/modelator/golang"
)

func FixedExecutions() [][]modelator.StepI {
	return [][]modelator.StepI{
		{
			Step{0, 0, None, "OK"},
			Step{1, 0, IncreaseA, "OK"},
			Step{1, 2, IncreaseB, "OK"},
			Step{2, 2, IncreaseA, "OK"},
			Step{2, 4, IncreaseB, "OK"},
			Step{2, 6, IncreaseB, "OK"},
			Step{2, 6, IncreaseB, "FAIL"},
		},
		{
			Step{0, 0, None, "OK"},
			Step{1, 0, IncreaseA, "OK"},
			Step{1, 2, IncreaseB, "OK"},
		},
	}
}

func TestFixedExecutions(t *testing.T) {
	testRuns := FixedExecutions()

	for i, testRun := range testRuns {
		name := fmt.Sprintf("test_%v", i)
		t.Run(name, func(t *testing.T) {
			initialState := &NumberSystem{}
			if err := modelator.Run(initialState, testRun); err != nil {
				t.Error(err)
			}
		})
	}
}

func TestModelBased(t *testing.T) {
	jsonTraces, err := modelator.GenerateJSONTracesFromTLATests("NumbersTest.tla", "Numbers.cfg")
	if err != nil {
		t.Error(err)
	}
	var tests map[string][][]Step
	json.Unmarshal([]byte(jsonTraces), &tests)
	for name, testRuns := range tests {
		for i, testRun := range testRuns {
			name := fmt.Sprintf("[test: %v, trace: %v]", name, i)
			t.Run(name, func(t *testing.T) {
				initialState := &NumberSystem{}
				testRunI := make([]modelator.StepI, len(testRun))
				for i, testStep := range testRun {
					testRunI[i] = testStep
				}
				if err := modelator.Run(initialState, testRunI); err != nil {
					t.Error(err)
				}
			})
		}
	}
}
