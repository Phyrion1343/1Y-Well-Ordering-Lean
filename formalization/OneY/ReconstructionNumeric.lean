import OneY.Reconstruction
import OneY.NumericGeometry

/-!
# Numerical mountain -> parent graph and top values -> reconstruction

The equality is derived from the actual difference computation and the
uniqueness theorem.  No canonicality property of an expanded graph is assumed.
-/

namespace OneY.Reconstruction

theorem numeric_rows_reconstruct (base : Numeric.Row)
    (hpos : ∀ c, 0 < base.value c) :
    Reconstructs (Numeric.mountain base hpos) (Numeric.topValue base)
      (fun r c => (Numeric.rows base r).value c) := by
  constructor
  · intro r c hr
    change Numeric.height base c < r at hr
    have hNotLive : ¬0 < (Numeric.rows base r).value c := by
      intro hLive
      have h := (Numeric.live_iff_le_height base (hpos c) r).mp hLive
      omega
    omega
  · intro c
    rfl
  · intro r c p hp
    change (Numeric.rows base r).forest.parent c = some p at hp
    change (Numeric.rows base r).value c =
      (Numeric.rows base r).difference c + (Numeric.rows base r).value p
    rw [Numeric.Row.difference, hp]
    exact (Nat.sub_add_cancel (Nat.le_of_lt
      ((Numeric.rows base r).parent_values hp).2)).symm

theorem value_numeric_mountain (base : Numeric.Row)
    (hpos : ∀ c, 0 < base.value c) :
    value (Numeric.mountain base hpos) (Numeric.topValue base) =
      (fun r c => (Numeric.rows base r).value c) :=
  (reconstructs_eq_value _ _ (numeric_rows_reconstruct base hpos)).symm

theorem value_numeric_cell (base : Numeric.Row)
    (hpos : ∀ c, 0 < base.value c) (r c : Nat) :
    value (Numeric.mountain base hpos) (Numeric.topValue base) r c =
      (Numeric.rows base r).value c := by
  rw [value_numeric_mountain]

theorem value_numeric_base (base : Numeric.Row)
    (hpos : ∀ c, 0 < base.value c) (c : Nat) :
    value (Numeric.mountain base hpos) (Numeric.topValue base) 0 c =
      base.value c := by
  rw [value_numeric_cell]
  rfl

theorem value_sequence_base (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (c : Nat) :
    value (Numeric.sequenceMountain s hs) (Numeric.topValue (Numeric.ofSequence s))
      0 c = s[c]?.getD 1 := by
  exact value_numeric_base (Numeric.ofSequence s) (Numeric.ofSequence_positive s hs) c

/-- Recomputing a higher-row parent after this unmodified reconstruction
recovers the original numerical row parent, by the just-proved value equality. -/
theorem restrictedParent_numeric_reconstruction (base : Numeric.Row)
    (hpos : ∀ c, 0 < base.value c) (r c : Nat) :
    Numeric.restrictedParent (Numeric.rows base r).forest
      (value (Numeric.mountain base hpos) (Numeric.topValue base) (r+1)) c =
        (Numeric.rows base (r+1)).forest.parent c := by
  rw [value_numeric_mountain]
  rfl

#print axioms numeric_rows_reconstruct
#print axioms value_numeric_mountain
#print axioms value_sequence_base
#print axioms restrictedParent_numeric_reconstruction

end OneY.Reconstruction
