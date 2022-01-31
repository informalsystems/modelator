package modelator_test

import (
	"testing"

	modelator "github.com/informalsystems/modelator/go/pkg/core"
)

func TestModelBased(t *testing.T) {
	_, err := modelator.GenerateJSONTracesFromTLATests("doesnotexist", "doesnotexist")
	if err == nil {
		t.Error("Modelator should have returned error.")
	}
}
