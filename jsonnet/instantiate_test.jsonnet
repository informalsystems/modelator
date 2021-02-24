local instantiate = import 'instantiate.jsonnet';
local expected = import 'instantiate_test_expected.json';


local Config = {
  AllNodes: instantiate.weighted_id_list("n", 100),
  TRUSTED_HEIGHT: 1,
  TARGET_HEIGHT: instantiate.weighted_integer(2, 10, function(x) x*x),
  TRUSTING_PERIOD: 1400,
  IS_PRIMARY_CORRECT: false,
  Test: instantiate.weighted_id([
    ["TestSuccess", 1],
    ["TestFailure", 1],
    ["Test2NotEnoughTrustSuccess", 2],
    ["Test2NotEnoughTrustFailure", 2],
    ["Test3NotEnoughTrustSuccess", 3],
    ["Test3NotEnoughTrustFailure", 3],
    ["TestNonMonotonicHeight", 4],
    ["TestHeaderFromFuture", 5],
  ]),
};

assert(instantiate.instances_upto_weight(Config, 100) == expected);

"PASS"
