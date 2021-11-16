/* Library for wrapping/unwrapping JSON-RPC envelopes */
/* Encodes the requirements from https://www.jsonrpc.org/specification */

local check = import 'check.jsonnet';

{
// ===== External interface =====

// ---- Construction of JSON-RPC -----

// A JSON-RPC request
request(id, method, params = null)::
  local x = 
    jsonrpc + 
    addId(id) +
    addMethod(method) + 
    addParams(params);
  x + this.validateRequest(x),

// A JSON-RPC notification
notification(method, params = null)::
  local x = 
    jsonrpc + 
    addMethod(method) + 
    addParams(params);
  x + this.validateNotification(x),

// A JSON-RPC result response
responseResult(id, result)::
  local x = 
    jsonrpc + 
    addId(id) +
    { result: result, }; // no restrictions on result
  x + this.validateResponseResult(x),

// A JSON-RPC general error response
responseError(id, code, message, data = null)::
  errorResponse(id, code, message, data),

// Specific JSON-RPC error responses

responseParseError(id, message = "Invalid JSON was received by the server", data = null):: 
  errorResponse(id, -32700, message, data),

responseInvalidRequest(id, message = "The JSON sent is not a valid Request object", data = null):: 
  errorResponse(id, -32600, message, data),

responseMethodNotFound(id, message = "The method does not exist / is not available", data = null):: 
  errorResponse(id, -32601, message, data),

responseInvalidParams(id, message = "Invalid method parameter(s)", data = null):: 
  errorResponse(id, -32602, message, data),

responseInternalError(id, message = "Internal JSON-RPC error", data = null):: 
  errorResponse(id, -32603, message, data),


// ---- Validation of incoming JSON-RPC -----

classifyRequest(x)::
  if validateNotification(x) then
    "notification"
  else if validateRequest(x) then
    "request"
  else
    null,

classifyResponse(x)::
  if validateResponseResult(x) then
    "result"
  else if validateResponseError(x) then
    "error"
  else
    null,

// Validates a JSON-RPC notification
validateNotification(x)::
  validateJsonRPC(x) + 
  validateMethod(x) +
  validateParams(x) +
  check.objectNotHas(x, 'id'),

// Validates a JSON-RPC request
validateRequest(x)::
  validateJsonRPC(x) + 
  validateMethod(x) +
  validateParams(x) + 
  validateId(x),

// Validates a JSON-RPC result
validateResponseResult(x)::
  validateJsonRPC(x) + 
  validateId(x) +
  check.objectHas(x, 'result') +
  check.objectNotHas(x, 'error'),


// Validates a JSON-RPC error
validateResponseError(x)::
  validateJsonRPC(x) + 
  validateId(x) +
  check.objectNotHas(x, 'result') +
  validateError(x),



// ===== Internal functions =====

local this = self,

local jsonrpc = {
  jsonrpc: "2.0",
},

local addId(id) =
  { id: id },

local addMethod(method) =
  { method: method },

local addParams(params) =
  { [if params != null then "params"]: params },

local addError(code, message, data) =
  { "error": { 
      [if data != null then "data"]: data,
      code: code,
      message: message
    }
  },

local errorResponse(id, code, message, data) = 
  local x = 
    jsonrpc + 
    addId(id) + 
    addError(code, message, data);
  x + this.validateResponseError(x),

local validateJsonRPC(x) =
  check.objectHas(x, 'jsonrpc')
    .and(check.equals(x.jsonrpc, jsonrpc.jsonrpc)),

local validateId(x) =
  check.objectHas(x, 'id').and(
    check.isString(x.id)
      .or(check.isInteger(x.id))
  ),

local validateMethod(x) =
  check.objectHas(x, 'method')
    .and(check.isString(x.method))
    .and(check.notStartsWith(x.method, "rpc.")),

local validateParams(x) =
  if std.objectHas(x, 'params') then
    check.isNull(x.params)
    .or(check.isArray(x.params))
    .or(check.isObject(x.params))
  else {},

local validateError(x) =
  check.objectHas(x, 'error').and(
    check.objectHas(x["error"], "code")
      .and(check.isInteger(x["error"].code)) +
    check.objectHas(x["error"], "message")
      .and(check.isString(x["error"].message))
  ),

}

