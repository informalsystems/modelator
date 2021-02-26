local weighted = import 'weighted_instance.jsonnet';
local expected = import 'weighted_instance_test_expected.json';


local Config = {
  AllNodes: weighted.id_list("n", 100),
  TRUSTED_HEIGHT: 1,
  TARGET_HEIGHT: weighted.integer(2, 10, function(x) x*x),
  TRUSTING_PERIOD: 1400,
  IS_PRIMARY_CORRECT: false,
  Test: weighted.id([
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

assert(weighted.instances_upto(Config, 100) == expected);

"PASS"
