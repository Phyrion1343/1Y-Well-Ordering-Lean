import OneY.Extraction

/-!
# Kernel-checked examples of inherited extraction

These examples use the executable definitions, with ordinary `decide`.
They are regression examples in addition to the general theorems.
-/

namespace OneY.Numeric.Examples

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def firstValues (a : Row) (n : Nat) : List Nat :=
  (List.range n).map a.value

example : firstValues (rows (ofSequence [1, 2, 4, 5, 8]) 1) 5 =
    [0, 1, 2, 1, 3] := by decide

example : firstValues (rows (ofSequence [1, 2, 4, 5, 8]) 2) 5 =
    [0, 0, 1, 0, 2] := by decide

/-- The earlier `1` is numerically smaller but is not an inherited ancestor. -/
example : (rows (ofSequence [1, 2, 4, 5, 8]) 2).forest.parent 4 = none := by decide

def extractedExample : Row := rawExtract (ofSequence [1, 3, 6, 8])
  (ofSequence_positive _ (by simp))

example : firstValues extractedExample 4 = [1, 2, 1, 2] := by decide

/-- Extraction keeps a different parent from recomputing from numbers alone. -/
theorem inherited_parent_example : extractedExample.forest.parent 3 = some 0 := by decide

example : (ofSequence [1, 2, 1, 2]).forest.parent 3 = some 2 := by decide

end OneY.Numeric.Examples

#print axioms OneY.Numeric.Examples.inherited_parent_example
