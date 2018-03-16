load(
  "@rules_tla//tla:tla.bzl",
  "tla_module", "tlc_test"
)

tla_module(
  name = "Peterson",
  src = "Peterson.tla",
)

tlc_test(
  name = "Peterson_tlc",
  cfg = "Peterson.cfg",
  module = ":Peterson",
  workers = 1,
  deadlock = False,
)
