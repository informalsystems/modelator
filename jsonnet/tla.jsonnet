// Library for manipulating TLA+ JSON representation

{
  local tla = self,

// ===== Construction functions =====


variable(name):: {
  variable: name
},

constant(name):: {
  constant: name
},

// Conjunction: args[0] /\ args[1] /\ ...
and(args):: {
  and: args
},

isAnd(expr)::
  std.isObject(expr) && std.objectHas(expr, "and") && std.isArray(expr.and),

plus(lhs, rhs):: {
  plus: lhs,
  arg: rhs
},

// Equality: lhs = rhs
eq(lhs, rhs):: {
  eq: lhs,
  arg: rhs
},

// Operator declaration: name(params) == body
operator(name, body, params = []):: {
  operator: name,
  params: params,
  body: body
},

// Operator application: name(args)
applyOp(name, args = []):: {
  applyOp: name,
  args: args
},

// Function application: name[arg]
applyFun(name, arg):: {
  applyFun: name,
  arg: arg
},

// One of the builtin sets
set(name):: {
  set: name
},

// Builtin Int set
Int:: tla.set("Int"),

// Set enumeration: {values}
enumSet(values):: {
  enumSet: values
},

// Apalache type annotation: expr <: type
typed(expr, type):: {
  lessColon: expr,
  arg: type
},

// String constant
str(string):: {
  str: string
},

// A key-value pair
pair(key, value):: {
  key: key,
  value: value
},

// Record: [ a1 |-> a2, b1 |-> b2, ...]
record(fieldPairs):: {
  record: fieldPairs
},

// Function definition: [ a1 \in T1, a2 \in T2 |-> body ] 
funDef(argPairs, body):: {
  funDef: body,
  where: argPairs
},

// Conditional expression: if cond then then_branch else else_branch
ifThenElse(cond, then_branch, else_branch):: {
  "if": cond,
  "then": then_branch,
  "else": else_branch 
},

// Prime (next state) expression: expr'
prime(expr):: {
  prime: expr
},

// Union of sets: lhs \union rhs
union(lhs, rhs):: {
  cup: lhs,
  arg: rhs
},

// Function domain: DOMAIN expr
domain(expr):: {
  domain: expr
},

// A TLA+ module has a name and a list of declarations
module(name, declarations):: {
  module: name,
  declarations: declarations
},


// ===== Decomposition functions =====

validateModule(module)::
  std.isObject(module) &&
  std.objectHas(module, "module") && std.isString(module.module) &&
  std.objectHas(module, "declarations") && std.isArray(module.declarations),

validateOperator(oper)::
  std.isObject(oper) &&
  std.objectHas(oper, "operator") && std.isString(oper.operator) &&
  std.objectHas(oper, "params") && std.isArray(oper.params) &&
  std.objectHas(oper, "body"),

moduleListVariables(module):: moduleList(module, "variable"),
moduleListConstants(module):: moduleList(module, "constant"),
moduleListOperators(module):: moduleList(module, "operator"),

moduleHasVariable(module, name):: moduleHas(module, "variable", name),
moduleHasConstant(module, name):: moduleHas(module, "constant", name),
moduleHasOperator(module, name):: moduleHas(module, "operator", name),

moduleGetVariable(module, name):: moduleGet(module, "variable", name),
moduleGetConstant(module, name):: moduleGet(module, "constant", name),
moduleGetOperator(module, name):: moduleGet(module, "operator", name),

moduleAddVariable(module, name)::
  if tla.moduleHasVariable(module, name) then
    error "Variable " + name + " already exists in module " + module.module
  else
    local vars = tla.moduleListVariables(module);
    local len = std.length(vars);
    local newDecls = if len != 0 then
      local last = vars[len-1];
      std.flatMap(
        function(decl)
          if std.objectHas(decl, "variable") && decl.variable == last then
            [decl, tla.variable(name)]
          else [decl]
        , module.declarations
      )
    else
      tla.variable(name) + module.declarations;
    module { declarations: newDecls},


moduleReplaceOperator(module, name, oper) ::
  local decls = std.map(
    function(decl)
      if std.objectHas(decl, "operator") && decl.operator == name then
        oper
      else 
        decl,
    module.declarations
  );
  module { declarations: decls },

// Add expr as a conjuction to the given module operator
moduleExtendOperator(module, name, expr)::
  local oper = tla.moduleGetOperator(module, name);
  if !tla.validateOperator(oper) then
    error "Invalid operator " + name + " in module " + module
  else
    local body = 
      if tla.isAnd(oper.body) then oper.body.and
      else [oper.body];
    local newBody = 
      if tla.isAnd(expr) then body + expr.and
      else body + [expr];
    tla.moduleReplaceOperator(module, name, oper { body: tla.and(newBody) }),



// ===== Internal functions =====

local moduleList(module, type) = 
  std.filterMap(
    function(decl) std.objectHas(decl, type) && std.isString(decl[type]),
    function(decl) decl[type],
    module.declarations
  ),
  
local moduleHas(module, type, name) = 
  local decls = std.filter(
    function(decl) std.objectHas(decl, type) && decl[type] == name,
    module.declarations
  );
  std.length(decls) > 0,

local moduleGet(module, type, name) = 
  local decls = std.filter(
    function(decl) std.objectHas(decl, type) && decl[type] == name,
    module.declarations
  );
  if std.length(decls) != 1 then 
    error "Non-singleton " + type + " declaration '" + name + "' in module " + module.name
  else 
    decls[0],

}




