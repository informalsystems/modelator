local jsonrpc = import 'jsonrpc.jsonnet';
local check = import 'check.jsonnet';

  assert(jsonrpc.request(1, "noParams") ==
  {
    "id": 1,
    "jsonrpc": "2.0",
    "method": "noParams"
  }
): "request with no params";

assert(
  jsonrpc.request(2, "arrayParams", [1, 2 ,"ok"]) ==
  {
   "id": 2,
   "jsonrpc": "2.0",
   "method": "arrayParams",
   "params": [
      1,
      2,
      "ok"
   ]
  }
): "request with array params";

assert(
  jsonrpc.request(3, "objectParams", {"name": "cosmos", "token": "atom"}) ==
  {
   "id": 3,
   "jsonrpc": "2.0",
   "method": "objectParams",
   "params": {
      "name": "cosmos",
      "token": "atom"
   }
  }
): "request with object params";

assert(
  jsonrpc.responseResult(4, "ok") ==
  {
   "id": 4,
   "jsonrpc": "2.0",
   "result": "ok"
  }
): "response ok";

assert(
  jsonrpc.responseError(5, 100, "some error") ==
  {
   "error": {
      "code": 100,
      "message": "some error"
   },
   "id": 5,
   "jsonrpc": "2.0"
  }  
): "response error";

assert(
  jsonrpc.responseError(6, 100, "some error", "some data") ==
  {
   "error": {
      "code": 100,
      "data": "some data",
      "message": "some error"
   },
   "id": 6,
   "jsonrpc": "2.0"
  } 
): "response error with data";

assert(check.all([
  jsonrpc.request([], "wrong id").expectFailsWith("expected one of alternatives"),
  jsonrpc.request(2, 3).expectFailsWith("expected string"),
  jsonrpc.request(3, "unstructured params", "params").expectFailsWith("expected one of alternatives"),
  jsonrpc.responseError(4, 1.23, "wrong error code").expectFailsWith("expected integer"),
  jsonrpc.responseError(4, 200, ["non-string error message"]).expectFailsWith("expected string"),
  jsonrpc.request(2, 3).expectFailsWith("expected string"),
  jsonrpc.request(2, 3).expectFailsWith("expected string"),
]));


assert(check.all([
   jsonrpc.validateRequest(
      {
      "id": 1,
      "jsonrpc": "2.0",
      "method": "arrayParams",
      "params": [
         1,
         2,
         "ok"
      ]
      }).expectOk(),
   jsonrpc.validateRequest(
      {
         "jsonrpc": "2.0",
         "method": "arrayParams",
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected object field 'id'"),
   jsonrpc.validateRequest(
      {
         "id": 2,
         "method": "arrayParams",
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected object field 'jsonrpc'"),
   jsonrpc.validateRequest(
      {
         "id": 2,
         "jsonrpc": "2.0",
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected object field 'method'"),
   jsonrpc.validateRequest(
      {
         "id": 2,
         "jsonrpc": "2.0",
         "method": "No params",
      }).expectOk(),
   jsonrpc.validateRequest(
      {
         "id": 2,
         "jsonrpc": "1.0",
         "method": "arrayParams",
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected equal"),
   jsonrpc.validateRequest(
      {
         "id": true,
         "jsonrpc": "2.0",
         "method": "arrayParams",
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected one of alternatives"),
   jsonrpc.validateRequest(
      {
         "id": 1,
         "jsonrpc": "2.0",
         "method": 2,
         "params": [
            1,
            2,
            "ok"
         ]
      }).expectFailsWith("expected string"),
   jsonrpc.validateRequest(
      {
         "id": 1,
         "jsonrpc": "2.0",
         "method": "rpc.method",
         "params": [
            1,
            2,
            "ok"
         ] 
      }).expectFailsWith("expected not starts with"),
   jsonrpc.validateRequest(
      {
         "id": 1,
         "jsonrpc": "2.0",
         "method": "arrayParams",
         "params": true   
      }).expectFailsWith("expected one of alternatives"),
   jsonrpc.validateResponseResult(
      {
         "id": 4,
         "jsonrpc": "2.0",
         "result": "ok"  
      }).expectOk(),
   jsonrpc.validateResponseResult(
      {
         "id": {id: 10},
         "jsonrpc": "2.0",
         "result": "ok"
   
      }).expectFailsWith("expected one of alternatives"),
   jsonrpc.validateResponseResult(
      {
         "id": 5,
         "jsonrpc": 2,
         "result": "ok"
   
      }).expectFailsWith("expected equal"),
   jsonrpc.validateResponseResult(
      {
         "id": 5,
         "jsonrpc": "2.0",   
      }).expectFailsWith("expected object field 'result'"),
   jsonrpc.validateResponseResult(
      {
         "jsonrpc": 2,
         "result": "ok"
   
      }).expectFailsWith("expected object field 'id'"),
   jsonrpc.validateResponseResult(
      {
         "id": 5,
         "result": "ok"
   
      }).expectFailsWith("expected object field 'jsonrpc'"),
   jsonrpc.validateResponseResult(
      {
         "jsonrpc": "2.0",
         "id": 5,
         "result": "ok",
         "error": {
            "code": 100,
            "message": "some error"
         },   
      }).expectFailsWith("unexpected object field 'error'"),
   jsonrpc.validateResponseError(
      {
         "error": {
            "code": 100,
            "message": "some error"
         },
         "id": 5,
         "jsonrpc": "2.0"
   
      }).expectOk(),
   jsonrpc.validateResponseError(
      {
         "id": 5,
         "jsonrpc": "2.0"
   
      }).expectFailsWith("expected object field 'error'"),
   jsonrpc.validateResponseError(
      {
         "error": {
            "message": "some error"
         },
         "id": 5,
         "jsonrpc": "2.0"   
      }).expectFailsWith("expected object field 'code'"),
   jsonrpc.validateResponseError(
      {
         "error": {
            "code": 100,
         },
         "id": 5,
         "jsonrpc": "2.0"   
      }).expectFailsWith("expected object field 'message'"),
   jsonrpc.validateResponseError(
      {
         "error": {
            "code": "100",
            "message": "some error" 
         },
         "id": 5,
         "jsonrpc": "2.0"  
      }).expectFailsWith("expected integer"),
   jsonrpc.validateResponseError(
      {
        "error": {
            "code": 100,
            "message": 3
         },
         "id": 5,
         "jsonrpc": "2.0"   
      }).expectFailsWith("expected string"),

]));

"PASS"







