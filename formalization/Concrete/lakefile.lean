import Lake

open Lake DSL

package «zero-y-concrete»

-- 固定源码与主工程相同；mathlib 使用该提交的官方源码归档。
require ZeroYBMS from ".."
require YesMetaZFC from "../../vendor/bms"
require mathlib from "../../vendor/mathlib"
require «lean-constructible-universe» from
  "../../vendor/cu"
require «bms-constructible-bridge» from
  "../../vendor/bms/ConstructibleBridge"

@[default_target]
lean_lib ZeroYConcrete

@[default_target]
lean_lib OneYTruth
