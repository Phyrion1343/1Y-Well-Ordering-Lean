-- Modified for the 1-Y bundled distribution: use local dependencies without automatic downloads.
import Lake

open Lake DSL

package «bms-constructible-bridge»

require YesMetaZFC from ".."
require «lean-constructible-universe» from "../../cu"

@[default_target]
lean_lib BMSConstructibleBridge
