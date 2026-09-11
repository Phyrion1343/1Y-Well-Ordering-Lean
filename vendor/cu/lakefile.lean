-- Modified for the 1-Y bundled distribution: use local dependencies without automatic downloads.
import Lake

open Lake DSL

package «lean-constructible-universe» where
  version := v!"1.0.0"

require mathlib from "../mathlib"

@[default_target]
lean_lib ConstructibleUniverse
