local check = import 'check.jsonnet';

local a = {
  id: 1,
  name: "a",
  sub: {
    id: 2,
    name: "b"
  },
};

local test1 = 
  check.objectHas(a, "id") +
  check.objectHas(a, "data").and(
    check.objectHas(a.data, "b")
  ) + 
  check.objectHas(a, "sub").and(
    check.objectHas(a.sub, "id").and(
      check.equals(a.sub.id, "2")
    )
  );

assert(check.all([
  test1.expectFailsWith("expected object field 'data'"),
  test1.expectFailsWith("expected equal"),
  test1.numErrors() == 2
]));

local test2 = 
  check.objectHas(a, "data1")
  .or(check.objectHas(a, "data2"))
;

assert(check.all([
  test2.expectFailsWith("expected one of alternatives"),
  test2.numErrors() == 1
]));

"PASS"
