// Run with `jrsonnet -o out.json test.jsonnet`

local lib = import 'weights.libjsonnet';

local Config = {
  AllNodes: lib.weighted_id_list("n", 100, function(x) x),
  TRUSTED_HEIGHT: 1,
  TARGET_HEIGHT: lib.weighted_integer(2, 10, function(x) x*x),
  TRUSTING_PERIOD: 1400,
  IS_PRIMARY_CORRECT: false,
  Test: lib.weighted_id([
    ["TestSuccess", 1],
    ["TestFailure", 1],
    ["Test2NotEnoughTrustSuccess", 2],
    ["Test2NotEnoughTrustFailure", 2],
    ["Test3NotEnoughTrustSuccess", 3],
    ["Test3NotEnoughTrustFailure", 3],
    ["TestNonMonotonicHeight", 4],
    ["TestHeaderFromFuture", 5],
  ]),

  weight:: function(x) x.AllNodes.weight * x.TARGET_HEIGHT.weight * x.Test.weight
};

lib.instantiate_upto_weight(Config, 100)