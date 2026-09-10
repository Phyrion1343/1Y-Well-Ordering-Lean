import Lake

open Lake DSL

package «zero-y-concrete»

-- 固定源码与主工程相同；mathlib 使用该提交的官方源码归档。
require ZeroYBMS from ".."
require YesMetaZFC from "../../research/BMS-Well-Ordering-Lean"
require mathlib from "../../.tools/mathlib4-eba3d887fc52c98627f4b81507c0efc3096e91b9"
require «lean-constructible-universe» from
  "../../.tools/cu-7f5a7d03"
require «bms-constructible-bridge» from
  "../../research/BMS-Well-Ordering-Lean/ConstructibleBridge"

@[default_target]
lean_lib ZeroYConcrete

@[default_target]
lean_lib OneYTruth
