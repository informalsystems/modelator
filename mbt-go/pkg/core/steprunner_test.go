package core

import "testing"

func TestModelBased(t *testing.T) {
	_, err := GenerateJSONTracesFromTLATests("doesnotexist", "doesnotexist")
	if err == nil {
		t.Error("Modelator should have returned error.")
	}
}
