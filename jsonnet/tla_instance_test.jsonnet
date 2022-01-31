local tla_instance = import 'tla_instance.jsonnet';
local lightclient = import "Lightclient_003_draft.json";
local tla = import 'tla.jsonnet';

local config =  {
      "AllNodes": [
         "n1", "n2"
      ],
      "IS_PRIMARY_CORRECT": false,
      "TARGET_HEIGHT": 4,
      "TRUSTED_HEIGHT": 1,
      "TRUSTING_PERIOD": 1400,
      "Test": "TestSuccess",
   };

local lightclient2 = tla_instance.instantiate(lightclient, config);

assert(tla.validateModule(lightclient2));
assert(tla.moduleListConstants(lightclient2) == []);
assert(tla.moduleGetOperator(lightclient2, "AllNodes") == 
  tla.operator("AllNodes", tla.enumSet([tla.str("n1"), tla.str("n2")]))
);
assert(tla.moduleGetOperator(lightclient2, "IS_PRIMARY_CORRECT") == 
  tla.operator("IS_PRIMARY_CORRECT", false)
);
assert(tla.moduleGetOperator(lightclient2, "TARGET_HEIGHT") == 
  tla.operator("TARGET_HEIGHT", 4)
);

"PASS"

