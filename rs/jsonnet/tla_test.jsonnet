local tla = import "tla.jsonnet";
local history = import "history.json";
local lightclient = import "Lightclient_003_draft.json";

local InitTest = tla.operator("InitTest",  
  tla.and([
    tla.applyOp("Init"),
    tla.eq("history",
      tla.funDef([
        tla.pair("n", tla.typed(tla.enumSet([]), tla.enumSet([tla.Int])))
      ],
      tla.str("NULL")
      )
    )
  ])
);

assert(InitTest == history.declarations[0]): "InitTest encoding";


local NextTest = tla.operator("NextTest",  
  tla.and([
    tla.applyOp("Next"),
    tla.eq(tla.prime("history"),
      tla.funDef(
        [tla.pair("n", 
          tla.union(tla.domain("history"), tla.enumSet([tla.prime("nprobes")]))
        )
        ],
        tla.ifThenElse(
          tla.eq("n", tla.prime("nprobes")),
          tla.record([
            tla.pair(tla.str("verdict"), "prevVerdict"),
            tla.pair(tla.str("now"), "prevNow"),
          ]),
          tla.applyFun("history", "n")
        )
      )
    ) 
  ])
);

assert(NextTest == history.declarations[1]): "NextTest encoding";

assert(tla.validateModule(tla.module("mod",[])));

assert(tla.moduleListVariables(lightclient) ==
  [
    "prevCurrent", "nextHeight", "prevNow", "nprobes", "lightBlockStatus",
    "now", "state", "latestVerified", "fetchedLightBlocks", "Faulty",
    "prevVerified", "prevVerdict", "blockchain"
  ]
): "Extract module variables";

assert(tla.moduleListConstants(lightclient) ==
  [
    "TRUSTING_PERIOD",  "IS_PRIMARY_CORRECT", "AllNodes", "TARGET_HEIGHT", "TRUSTED_HEIGHT"
  ]
): "Extract module constants";

assert(tla.moduleHasVariable(lightclient, "now"));
assert(tla.moduleHasOperator(lightclient, "Init"));

assert(tla.moduleGetVariable(lightclient, "now") == tla.variable("now"));

assert(tla.moduleGetOperator(lightclient, "ULTIMATE_HEIGHT") 
  == tla.operator("ULTIMATE_HEIGHT", tla.plus("TARGET_HEIGHT", 1)));

local lightclient2 = tla.moduleExtendOperator(lightclient, "ULTIMATE_HEIGHT", tla.eq(1,1));

assert(tla.moduleGetOperator(lightclient2, "ULTIMATE_HEIGHT") 
   == tla.operator("ULTIMATE_HEIGHT", tla.and([tla.plus("TARGET_HEIGHT", 1), tla.eq(1,1)])));

assert(tla.moduleGetOperator(lightclient2, "Init") 
  == tla.operator("Init", tla.and([
    tla.applyOp("BC!InitToHeight"),
    tla.applyOp("LCInit"),
  ])));

local lightclient3 = tla.moduleExtendOperator(lightclient, "Init", tla.eq(1,1));

assert(tla.moduleGetOperator(lightclient3, "Init") 
  == tla.operator("Init", tla.and([
    tla.applyOp("BC!InitToHeight"),
    tla.applyOp("LCInit"),
    tla.eq(1,1)
  ])));

local lightclient4 = tla.moduleAddVariable(lightclient3, "history");

assert(tla.moduleListVariables(lightclient4) == 
  tla.moduleListVariables(lightclient) + ["history"]
);

"PASS"

