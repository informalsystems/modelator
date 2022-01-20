package golang

/*
#cgo linux,amd64 LDFLAGS: -L${SRCDIR}/../target/x86_64-unknown-linux-gnu/release -lmodelatorc -ldl -lm
#cgo darwin,amd64 LDFLAGS: -L${SRCDIR}/../target/x86_64-apple-darwin/release -lmodelatorc -framework Security
#cgo windows,amd64 LDFLAGS: -L${SRCDIR}/../target/x86_64-pc-windows-gnu/release -lmodelatorc -lws2_32 -lole32 -luserenv -lbcrypt
#cgo CFLAGS: -I${SRCDIR}/../rust/ffi/src
#include <lib.h>
*/
import "C"

import (
	"fmt"
	"log"
)

// StepI stores action and a view of state after executing the action on current state
type StepI interface{}

// StepRunner interface which a system state should implement
type StepRunner interface {
	InitialStep(StepI) error
	NextStep(StepI) error
}

// StepMismatch error when system state does not match with step view
type StepMismatch struct {
	Expected StepI
	Observed StepRunner
	Outcome  string
}

func (e StepMismatch) Error() string {
	return fmt.Sprintf("expected: %v, observed: %v, outcome: %v", e.Expected, e.Observed, e.Outcome)
}

// ModelatorError when modelator throws an error
type ModelatorError string

func (e ModelatorError) Error() string {
	return fmt.Sprintf("[Modelator]: %v", string(e))
}

// Run performs series of steps on system state
func Run(state StepRunner, steps []StepI) (err error) {
	for i, step := range steps {
		if i == 0 {
			err = state.InitialStep(step)
		} else {
			err = state.NextStep(step)
		}
		if err != nil {
			return err
		}
	}
	return nil
}

// GenerateJSONTracesFromTLATests generates model traces from TLA specs and tests
func GenerateJSONTracesFromTLATests(tlaFile, cfgFile string) (string, error) {
	cTlaFile := C.CString(tlaFile)
	cCfgFile := C.CString(cfgFile)
	log.Printf("Generating traces using Modelator cgo-binding...")
	res, _ := C.generate_json_traces_from_tla_tests_rs(cTlaFile, cCfgFile)
	// https://utcc.utoronto.ca/~cks/space/blog/programming/GoCgoErrorReturns
	// ignoring errno from C
	// log.Printf("errno: %v\n", errno.(syscall.Errno))
	if res.error != nil {
		return "", ModelatorError(C.GoString(res.error))
	}
	return C.GoString(res.data), nil
}
