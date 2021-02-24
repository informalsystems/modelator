/* Library for instantiation of weighted configs */

{

manifest: {
  module: {
      name : "instantiate_weighted",
      description: "A module to generated instances of a weighted JSON configuration", 
      "version": "0.1.0",
      "methods": [ "instances_upto_weight" ]
    },
  instances_upto_weight: {
      name : "instances_upto_weight",
      description: "generate all instances of a weighted JSON configuration up to the given weight", 
      "inputs": {
        "config": "weighted_jsonnet",
        "max_weight": "integer"
      },
      "results": {
        "instances": ["json"]
      },
      "errors": {
        "message": "string",
        "output": "string"
      }
    }
}, 

// Instantiate the given config up to the maximum instance weight
// The instance weight is currently displayed for debugging purposes
instances_upto_weight(config, max_weight):: 
  local instances = instantiate(std.objectFields(config), config);

  local weighted_instances = std.map(function(obj) obj + {instance_weight: object_weight(obj)}, instances);
  std.filterMap(function(obj) obj.instance_weight <=  max_weight, replace_weighted_object_values, weighted_instances),


// Synonyms for some std functions
local range = std.range,
local length = std.length,

// Generates a list of identifiers with the given prefix, and suffixes from 1 to max
local id_list(prefix, max) = [
   prefix + x for x in range(1, max)
],

// A weighted integer. The default weight is the integer value itself
weighted_integer(min, max, weight = function(x) x):: { 
  min: min,
  max: max,
  value:: function(x) x,
  weight:: weight,
},

// A weighted list of identifiers. The default weight is the length of the list
weighted_id_list(prefix, max, weight = function(x) x):: { 
  min: 1,
  max: max,
  value:: function(x) id_list(prefix, x),
  weight:: weight,
},

// A weighted identifier. Each of the possible identifiers comes with its own weight
weighted_id(ids_with_weights):: { 
  min: 0,
  max: length(ids_with_weights)-1,
  value:: function(x) ids_with_weights[x][0],
  weight:: function(x) ids_with_weights[x][1],
},

// Is this a weighted object
local is_weighted_object(obj) = 
  std.isObject(obj) &&
  std.objectHasAll(obj, "min") &&
  std.objectHasAll(obj, "max") &&
  std.objectHasAll(obj, "value") &&
  std.objectHasAll(obj, "weight"),

// Instantiate a weighted object into an array
local instantiate_weighted(obj) = [
  {
    value:: obj.value(x),
    weight:: obj.weight(x),
  },
  for x in range(obj.min,obj.max)
],


// A recursive function that instantiates the given fields in an object
local instantiate(fields, obj) = 
  if length(fields) != 0 then 
    local field = fields[0];
    local rest = fields[1:];
    if is_weighted_object(obj[field]) then
      local weighted_instances = instantiate_weighted(obj[field]);
      local extend_with(obj, field, x) = obj + {[field]: x, weighted_fields:: obj.weighted_fields+[field],};
      std.flatMap(function(x) [extend_with(obj2, field, x) for obj2 in instantiate(rest, obj)],  weighted_instances)
    else
      instantiate(rest, obj)
  else [obj + {weighted_fields::[]}],

// If the given object is a weighted value, replace it with its value dropping the weight
local replace_weighted_value(obj) = 
  if std.isObject(obj) && std.objectHasAll(obj, "value") && std.objectHasAll(obj, "weight") then
    obj.value
  else
    obj,

// Replace all weighed value objects with their values dropping the weights
local replace_weighted_object_values(obj) =
  std.mapWithKey(function(field, value) replace_weighted_value(value), obj),

local object_weight(obj) = 
  if std.objectHasAll(obj, "weight") then
    obj.weight(obj)
  else // calculate the default weight as the product of all weighted fields
    std.foldl(function(prod,field) prod*obj[field].weight, obj.weighted_fields, 1),


}
