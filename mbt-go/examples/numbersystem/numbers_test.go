package numbers

import (
	"encoding/json"
	"fmt"
	"testing"

	"github.com/informalsystems/gopherator/pkg/core"
)

func FixedExecutions() [][]core.StepI {
	return [][]core.StepI{
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
			if err := core.Run(initialState, testRun); err != nil {
				t.Error(err)
			}
		})
	}
}

func TestModelBased(t *testing.T) {
	jsonTraces, err := core.GenerateJSONTracesFromTLATests("NumbersTest.tla", "Numbers.cfg")
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
				testRunI := make([]core.StepI, len(testRun))
				for i, testStep := range testRun {
					testRunI[i] = testStep
				}
				if err := core.Run(initialState, testRunI); err != nil {
					t.Error(err)
				}
			})
		}
	}
}
