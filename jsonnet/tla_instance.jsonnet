/* Module to instantiate TLA+ models using configuration */

local tla = import "tla.jsonnet";
local check = import "check.jsonnet";

{

manifest: {
  module: {
      name : "tla_instance",
      description: "A module to generate instances of TLA+ combined with configuration", 
      version: "0.1.0",
      methods: [ "instantiate" ]
    },
  instantiate: {
      description: "intstantiate a TLA+ model by substituting values for constants from a config", 
      inputs: {
        model: "json-tla",
        config: "json"
      },
      results: {
        instance: "json-tla"
      },
      errors: {
        message: "string",
        output: "string"
      }
    }
}, 

local constToTla(const) = 
  if check.isInteger(const).ok() then
    const
  else if std.isBoolean(const) then
    const
  else if std.isString(const) then
    tla.str(const)
  else if check.isArray(const).ok() then
    tla.enumSet(std.map(constToTla, const))
  else 
    error "cannot map to TLA+: " + const,

local configToOperator(config, const) =
  if check.objectHas(config, const).ok() then
    tla.operator(const, constToTla(config[const]))
  else
    error "configuration is missing for constant " + const,

instantiate(model, config)::
  assert(tla.validateModule(model)): "failed to parse TLA+ module";
  local instantiateConstant(decl) = 
    if tla.declarationIsConstant(decl) then
      configToOperator(config, decl.constant)
    else
      decl;

  model { declarations: std.map(instantiateConstant,model.declarations) },

}
