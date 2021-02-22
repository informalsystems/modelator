local tla = import "tla.jsonnet";
local history = import "history.jsonnet";
local lightclient = import "Lightclient_003_draft.json";


local moduleWithHistory = history.extendModuleWithHistory(lightclient, [["verdict", "prevVerdict"],["now", "prevNow"]]);

assert(tla.moduleGetOperator(moduleWithHistory, "Init") == 
  {
      "body": {
        "and": [
            {
              "applyOp": "BC!InitToHeight",
              "args": [ ]
            },
            {
              "applyOp": "LCInit",
              "args": [ ]
            },
            {
              "arg": {
                  "funDef": {
                    "str": "NULL"
                  },
                  "where": [
                    {
                        "key": "n",
                        "value": {
                          "arg": {
                              "enumSet": [
                                {
                                    "set": "Int"
                                }
                              ]
                          },
                          "lessColon": {
                              "enumSet": [ ]
                          }
                        }
                    }
                  ]
              },
              "eq": "history"
            },
            {
              "arg": 0,
              "eq": "historyLen"
            }
        ]
      },
      "operator": "Init",
      "params": [ ]
  }
);

assert(tla.moduleGetOperator(moduleWithHistory, "Next") == 
  {
      "body": {
        "and": [
            {
              "arg": {
                  "str": "working"
              },
              "eq": "state"
            },
            {
              "or": [
                  {
                    "applyOp": "VerifyToTargetLoop",
                    "args": [ ]
                  },
                  {
                    "applyOp": "VerifyToTargetDone",
                    "args": [ ]
                  }
              ]
            },
            {
              "applyOp": "BC!AdvanceTime",
              "args": [ ]
            },
            {
              "arg": {
                  "arg": 1,
                  "plus": "historyLen"
              },
              "eq": {
                  "prime": "historyLen"
              }
            },
            {
              "arg": {
                  "funDef": {
                    "else": {
                        "applyFun": "history",
                        "arg": "n"
                    },
                    "if": {
                        "arg": "historyLen",
                        "eq": "n"
                    },
                    "then": {
                        "record": [
                          {
                              "key": {
                                "str": "verdict"
                              },
                              "value": "prevVerdict"
                          },
                          {
                              "key": {
                                "str": "now"
                              },
                              "value": "prevNow"
                          }
                        ]
                    }
                  },
                  "where": [
                    {
                        "key": "n",
                        "value": {
                          "arg": {
                              "enumSet": [
                                "historyLen"
                              ]
                          },
                          "cup": {
                              "domain": "history"
                          }
                        }
                    }
                  ]
              },
              "eq": {
                  "prime": "history"
              }
            }
        ]
      },
      "operator": "Next",
      "params": [ ]
  }
);

"PASS"



