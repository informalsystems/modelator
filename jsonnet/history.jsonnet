// Library for history tracking

local tla = import "tla.jsonnet";

{

// ===== External interface =====

// Extends the module with history tracking; vars is the a the array of variables to capture.
// Each variable in vars should be one of the following:
// - a string name, meaning to capture the state variable with the same name 
// - [name, expr], meaning that the TLA+ expression expr should be captured as name
// The following assumptions are made:
// - the module contains neither "history" or "historyLen" variables
// - the module has "Init" and "Next" operators
extendModuleWithHistory(module, vars):: 
  local m1 = tla.moduleAddVariable(module, "history");
  local m2 = tla.moduleAddVariable(m1, "historyLen");
  local m3 = tla.moduleExtendOperator(m2, "Init", initHistoryPredicate);
  tla.moduleExtendOperator(m3, "Next", nextHistoryPredicate(vars)),


// ===== Internal functions =====

// Constructs extension to the Init predicate
local initHistoryPredicate = 
  tla.and([
  tla.eq("history", 
    tla.funDef([
      tla.pair("n", tla.typed(tla.enumSet([]), tla.enumSet([tla.Int])))
    ],
    tla.str("NULL")
    )
  ),
  tla.eq("historyLen", 0)
  ]),


// Constructs extension to the Next predicate
local nextHistoryPredicate(vars) = 
  tla.and([
    tla.eq(tla.prime("historyLen"), tla.plus("historyLen", 1)),
    tla.eq(tla.prime("history"),
      tla.funDef(
        [tla.pair("n", 
          tla.union(tla.domain("history"), tla.enumSet(["historyLen"]))
        )
        ],
        tla.ifThenElse(
          tla.eq("n", "historyLen"),
          tla.record(
            std.map(function (v) 
              if std.isString(v) then
                tla.pair(tla.str(v), v)
              else if std.isArray(v) && std.length(v) == 2 && std.isString(v[0]) then
                tla.pair(tla.str(v[0]), v[1])
              else
                error "Wrong format of variables when constructing next history predicate"
            , vars)
          ),
          tla.applyFun("history", "n")
        )
      )
    ) 
  ]),

}



