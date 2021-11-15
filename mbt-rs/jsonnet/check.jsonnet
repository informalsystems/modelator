// Library for unit checking

/* Example: 

  local res = 
    check.objectHas(req, 'id') +
    check.objectHas(req, 'jsonrpc') + 
    check.objectHas(req, 'method');
  
  res.ok() // if were all checks successful
  res.fail() // if some checks were not successful
  res.errors() // list encountered errors

*/

{
local check = self,

// A mixin for error handling
mixin():: {
  ok()::
    !self.hasErrors(),

  expectOk(msg = "expected to succeed"):: 
    assert(self.ok()) : msg + "\n" + std.manifestJson(self.errors());
    true,

  fails()::
    self.hasErrors(),

  expectFails(msg = "expected to fail")::
    assert(self.fails()) : msg + "\n" + std.manifestJson(self.errors());
    true,

  failsWith(err)::
    std.filter(
      function(x) x == err || std.isArray(x) && x[0] == err, 
      self.errors())
    != [],

  expectFailsWith(err, msg = "expected to fail")::
    assert(self.failsWith(err)) : msg + "\n" + std.manifestJson(self.errors());
    true,

  errors():: 
   if self.hasErrors() then
      self.CHECK_ERRORS
   else
      [],

  numErrors():: 
   std.length(self.errors()),

  lastError()::
    self.errors()[self.numErrors()-1],

  lastErrorMsg()::
    local err = self.lastError();
    if std.isArray(err) then
      err[0]
    else err,

  lastErrorData()::
    local err = self.lastError();
    if std.isArray(err) then
      err[1]
    else null,


  and(next):: 
    if self.ok() then
      next
    else
      self, 

  or(next)::
    if self.ok() then
      self
    else if next.ok() then
      next
    else
      local msg = "expected one of alternatives";
      local getErrors = function(x)
        if x.numErrors() == 1 then
          if x.lastErrorMsg() == msg then
            x.lastErrorData()
          else
            x.errors()
        else
          [x.errors()];
      check.throw(msg, getErrors(self) + getErrors(next)),
      

  hasErrors():: 
    std.isObject(self) && 
    std.objectHasAll(self, "CHECK_ERRORS") && 
    std.length(self.CHECK_ERRORS) != 0,
},


throw(msg, data = null):: check.mixin() + {
  CHECK_ERRORS+:: if data == null then [msg] else [[msg, data]],
},

objectHas(obj, field):: check.mixin() +
  if !std.isObject(obj) then
    check.throw("expected an object", obj)
  else if !std.objectHas(obj, field) then
    check.throw("expected object field '" + field + "'", obj)
   else
    {},

objectNotHas(obj, field):: check.mixin() +
  if !std.isObject(obj) then
    check.throw("expected an object", obj)
  else if std.objectHas(obj, field) then
    check.throw("unexpected object field '" + field + "'", obj)
   else
    {},


equals(lhs, rhs):: check.mixin() +
  if lhs != rhs then
    check.throw("expected equal", [lhs, rhs])
  else
   {},

isString(x):: check.mixin() +
  if !std.isString(x) then
    check.throw("expected string", x)
  else
   {},

startsWith(str, x):: check.mixin() +
  if !std.isString(str) then
    check.throw("expected a string", str)
  else if !std.isString(x) then
    check.throw("expected a string", x)
  else if !std.startsWith(str, x) then
    check.throw("expected starts with", [str, x])
  else
   {},

notStartsWith(str, x):: check.mixin() +
  if !std.isString(str) then
    check.throw("expected a string", str)
  else if !std.isString(x) then
    check.throw("expected a string", x)
  else if std.startsWith(str, x) then
    check.throw("expected not starts with", [str, x])
  else
   {},


isInteger(x):: check.mixin() +
  if !(std.isNumber(x) && x % 1 == 0) then
    check.throw("expected integer", x)
  else
   {},

isNull(x):: check.mixin() +
  if x != null then
    check.throw("expected null", x)
  else
   {},

isArray(x):: check.mixin() +
  if !std.isArray(x) then
    check.throw("expected array", x)
  else
   {},

isObject(x):: check.mixin() +
  if !std.isObject(x) then
    check.throw("expected object", x)
  else
   {},


// Expects arr to be an array of booleans
// Computes conjunction
all(arr):: 
  std.foldl(function(x,y) x && y, arr, true)
}

