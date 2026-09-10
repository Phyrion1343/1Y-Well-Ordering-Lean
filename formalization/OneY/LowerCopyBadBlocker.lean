import OneY.LowerCopyBlocker
import OneY.ReconstructionComparisonPrefix

/-! # Bad-parent blocker transport, including the reference-floor boundary -/

namespace OneY.LowerCopy.Context

open Reconstruction

theorem inCone_iff_of_same_high_parent (C : Context) {r c z p : Nat}
    (hr : C.floor ≤ r) (hC : (C.mountain.row r).parent c = some p)
    (hZ : (C.mountain.row r).parent z = some p) : C.InCone c ↔ C.InCone z := by
  constructor
  · intro hCone
    by_cases hOut : C.InCone z
    · exact hOut
    · exact False.elim (C.high_parent_outside hr hOut hZ (C.high_parent_inCone hCone hr hC))
  · intro hCone
    by_cases hOut : C.InCone c
    · exact hOut
    · exact False.elim (C.high_parent_outside hr hOut hC (C.high_parent_inCone hCone hr hZ))

/-- The parent of the row immediately above the transported candidate row.
At the floor itself this is the bottom reference row, not the lifted contour. -/
theorem parent_succ_rowCopy (C : Context) {s p u : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hp : (C.mountain.row (u+1)).parent s = some p) (b : Nat) :
    C.parent (C.rowCopy b s u+1) (C.coordinates.parentCopy b s) =
      some (C.coordinates.parentCopy b p) := by
  by_cases hBelow : u < C.floor
  · rw [C.rowCopy_low hBelow]
    by_cases hStrict : u+1 < C.floor
    · have ht := C.parent_rowCopy hx (by omega) hp b
      rwa [C.rowCopy_low hStrict] at ht
    · have hFloor : u+1 = C.floor := by omega
      rw [hFloor] at hp ⊢
      by_cases hCone : C.InCone s
      · have hpCone := C.high_parent_inCone hCone (Nat.le_refl _) hp
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs),
          C.coordinates.parentCopy_bad b (C.root_le_of_inCone hpCone)]
        change C.parent C.floor (C.coordinates.encode s b) = _
        rw [C.parent_encode_reference hs hx hCone b (Nat.le_refl _) (by omega), hp, Option.map_some]
      · have ht := C.parent_rowCopy hx (by omega) hp b
        rwa [C.rowCopy_outside hCone] at ht
  · have hu : C.floor ≤ u := by omega
    by_cases hCone : C.InCone s
    · rw [rowCopy, if_pos ⟨hCone, hu⟩]
      have ht := C.parent_rowCopy hx (by omega) hp b
      rw [rowCopy, if_pos ⟨hCone, by omega⟩] at ht
      have he : u+1+b*C.rise = u+b*C.rise+1 := by omega
      rwa [he] at ht
    · rw [C.rowCopy_outside hCone]
      have ht := C.parent_rowCopy hx (by omega) hp b
      rwa [C.rowCopy_outside hCone] at ht

theorem rowCopy_eq_of_common_next_parent (C : Context) {s z p u : Nat}
    (hS : (C.mountain.row (u+1)).parent s = some p)
    (hZ : (C.mountain.row (u+1)).parent z = some p) (b : Nat) :
    C.rowCopy b s u = C.rowCopy b z u := by
  by_cases hLow : u < C.floor
  · rw [C.rowCopy_low hLow, C.rowCopy_low hLow]
  · have hCone := C.inCone_iff_of_same_high_parent (by omega) hS hZ
    unfold rowCopy
    by_cases hCS : C.InCone s
    · rw [if_pos ⟨hCS, by omega⟩, if_pos ⟨hCone.mp hCS, by omega⟩]
    · rw [if_neg (fun h => hCS h.1), if_neg (fun h => hCS (hCone.mpr h.1))]

theorem keyLE_succ_rowCopy (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {u c z p : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hC : (C.mountain.row (u+1)).parent c = some p)
    (hZ : (C.mountain.row (u+1)).parent z = some p)
    (hKey : KeyLEFrom C.mountain oldTop (u+1+1) c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop (C.rowCopy b c u+1+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have hcLive := C.mountain.parent_source hC
  have hzLive := C.mountain.parent_source hZ
  have hInitial := hC.trans hZ.symm
  by_cases hBelow : u < C.floor
  · rw [C.rowCopy_low hBelow]
    by_cases hStrict : u+1 < C.floor
    · exact C.keyLE_low_start hRegular oldTop newTop hUpper hz hzc hcx hcLive hzLive hStrict hInitial hKey b
    · have he : u+1 = C.floor := by omega
      rw [he] at hcLive hzLive hInitial hKey ⊢
      exact C.keyLE_floor_start hRegular oldTop newTop hUpper hz hzc hcx hcLive hzLive hInitial hKey b
  · have hu : C.floor ≤ u := by omega
    have hCone := C.inCone_iff_of_same_high_parent (by omega) hC hZ
    by_cases hCS : C.InCone c
    · rw [rowCopy, if_pos ⟨hCS, hu⟩]
      have ht := C.keyLE_lifted_start hRegular oldTop newTop hUpper hz hzc hcx hcLive hzLive
        (by omega) hCS (hCone.mp hCS) hInitial hKey b
      have he : u+1+b*C.rise+1 = u+b*C.rise+1+1 := by omega
      rwa [he] at ht
    · rw [C.rowCopy_outside hCS]
      exact C.keyLE_outside_start hRegular oldTop newTop hUpper hz hzc hcx hcLive hzLive
        (by omega) hCS (fun h => hCS (hCone.mpr h)) hInitial hKey b

theorem bad_blocker_path (C : Context) {s z q p u : Nat}
    (_hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hQ : (C.mountain.row u).parent s = some q)
    (hS : (C.mountain.row (u+1)).parent s = some p)
    (hZ : (C.mountain.row (u+1)).parent z = some p)
    (hBad : C.coordinates.y ≤ p)
    (hPath : z = q ∨ (C.mountain.row (u+1)).Ancestor z q) (b : Nat) :
    C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
      (C.row (C.rowCopy b s u+1)).Ancestor
        (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
  rcases hPath with he | ha
  · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
  · apply Or.inr
    have hQLt := (C.mountain.row u).parent_left hQ
    have hPZLt := (C.mountain.row (u+1)).parent_left hZ
    have hZLt := ha.lt
    by_cases hBelow : u < C.floor
    · rw [C.rowCopy_low hBelow]
      by_cases hStrict : u+1 < C.floor
      · exact C.low_ancestor_copy hStrict ha (by omega) b
      · have he : u+1 = C.floor := by omega
        rw [he] at ha hS hZ ⊢
        have hCone := C.inCone_iff_of_same_high_parent (Nat.le_refl _) hS hZ
        by_cases hCS : C.InCone s
        · have hCZ := hCone.mp hCS
          have hCQ : C.InCone q := by
            by_cases hOut : C.InCone q
            · exact hOut
            · exact False.elim (C.high_ancestor_outside (Nat.le_refl _) hOut ha hCZ)
          rw [C.coordinates.parentCopy_bad b (by omega), C.coordinates.parentCopy_bad b (by omega)]
          exact C.reference_ancestor_copy hCQ ha (by omega) b (Nat.le_refl _) (by omega)
        · have hOutZ : ¬ C.InCone z := fun h => hCS (hCone.mpr h)
          have hOutQ : ¬ C.InCone q := fun h => hOutZ (C.high_ancestor_inCone (Nat.le_refl _) h ha)
          exact C.outside_ancestor_copy (Nat.le_refl _) hOutQ ha (by omega) b
    · have hu : C.floor ≤ u := by omega
      have hCone := C.inCone_iff_of_same_high_parent (by omega) hS hZ
      by_cases hCS : C.InCone s
      · have hCZ := hCone.mp hCS
        have hCQ : C.InCone q := by
          by_cases hOut : C.InCone q
          · exact hOut
          · exact False.elim (C.high_ancestor_outside (by omega) hOut ha hCZ)
        rw [rowCopy, if_pos ⟨hCS, hu⟩,
          C.coordinates.parentCopy_bad b (by omega), C.coordinates.parentCopy_bad b (by omega)]
        have he : u+b*C.rise+1 = u+1+b*C.rise := by omega
        rw [he]
        exact C.lifted_ancestor_copy (by omega) hCQ ha (by omega) b
      · have hOutZ : ¬ C.InCone z := fun h => hCS (hCone.mpr h)
        have hOutQ : ¬ C.InCone q := fun h => hOutZ (C.high_ancestor_inCone (by omega) h ha)
        rw [C.rowCopy_outside hCS]
        exact C.outside_ancestor_copy (by omega) hOutQ ha (by omega) b

theorem restrictedParent_bad_copy_of_blocker (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hOldPositive : ∀ c, 0 < oldTop c) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder oldTop newTop)
    (hOldCanonical : ∀ r i, Numeric.restrictedParent (C.mountain.row r)
      (value C.mountain oldTop (r+1)) i = (C.mountain.row (r+1)).parent i)
    {u s q p z : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hQ : (C.mountain.row u).parent s = some q)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (hZ : z = q ∨ (C.mountain.row (u+1)).Ancestor z q)
    (hZParent : (C.mountain.row (u+1)).parent z = some p)
    (hOldUpper : value C.mountain oldTop (u+1) s ≤ value C.mountain oldTop (u+1) z)
    (b : Nat)
    (hHigher : ∀ r, C.rowCopy b s u+1 ≤ r → ∀ i, i ≤ C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row (C.rowCopy b s u))
        (value C.toRowMountain newTop (C.rowCopy b s u+1)) i = C.parent (C.rowCopy b s u+1) i) :
    Numeric.restrictedParent (C.row (C.rowCopy b s u)) (value C.toRowMountain newTop (C.rowCopy b s u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have hQLt := (C.mountain.row u).parent_left hQ
  have hZLt : z < s := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hPZLt := (C.mountain.row (u+1)).parent_left hZParent
  have hZAfter : C.coordinates.y < z := by omega
  have hInitial := hP.trans hZParent.symm
  have hOldNext : value C.mountain oldTop (u+1+1) s ≤ value C.mountain oldTop (u+1+1) z := by
    rw [value_recurrence C.mountain oldTop hP, value_recurrence C.mountain oldTop hZParent] at hOldUpper
    omega
  have hOldKey := (keyLEFrom_iff_value_le C.mountain oldTop hOldPositive (u+1)
    (fun r _ => hOldCanonical r) (C.mountain.parent_source hP)
    (C.mountain.parent_source hZParent) hInitial).mpr hOldNext
  have hNewKey := C.keyLE_succ_rowCopy hRegular oldTop newTop hUpper hZAfter hZLt hx hP hZParent hOldKey b
  have hNewP := C.parent_succ_rowCopy hs hx hP b
  have hNewZP := C.parent_succ_rowCopy hZAfter (by omega) hZParent b
  have hSame := C.rowCopy_eq_of_common_next_parent hP hZParent b
  rw [← hSame] at hNewZP
  have hNewQ := C.parent_rowCopy hx (by omega) hQ b
  have hNewZLt : C.coordinates.parentCopy b z < C.coordinates.parentCopy b s := by
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hZAfter), C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
    omega
  have hNewNext := (keyLEFrom_iff_value_le_prefix C.toRowMountain newTop hPositive
    (C.rowCopy b s u+1) (C.coordinates.parentCopy b s+1)
    (fun r hr i hi => hHigher r hr i (by omega)) (by omega) (by omega)
    (C.parent_source hNewP) (C.parent_source hNewZP) (hNewP.trans hNewZP.symm)).mp hNewKey
  have hNewUpper : value C.toRowMountain newTop (C.rowCopy b s u+1) (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop (C.rowCopy b s u+1) (C.coordinates.parentCopy b z) := by
    rw [value_recurrence C.toRowMountain newTop hNewP,
      value_recurrence C.toRowMountain newTop hNewZP]
    omega
  exact Numeric.restrictedParent_eq_of_blocker (C.reconstructedRow newTop hPositive (C.rowCopy b s u+1))
    (C.row (C.rowCopy b s u)) hNewQ hNewP (C.nested_succ _ hNewP) hPrefix
    (C.bad_blocker_path hs hx hQ hP hZParent hBad hZ b) hNewZP hNewUpper

/-- All old nonempty bad-parent rows, including the floor boundary and lifted
contours. The only correctness hypotheses on the new layer are the already
restored higher rows and strict left prefix of the row under construction. -/
theorem restrictedParent_bad_copy (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hOldPositive : ∀ c, 0 < oldTop c) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder oldTop newTop)
    (hOldCanonical : ∀ r i, Numeric.restrictedParent (C.mountain.row r)
      (value C.mountain oldTop (r+1)) i = (C.mountain.row (r+1)).parent i)
    {u s p : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (b : Nat)
    (hHigher : ∀ r, C.rowCopy b s u+1 ≤ r → ∀ i, i ≤ C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row (C.rowCopy b s u))
        (value C.toRowMountain newTop (C.rowCopy b s u+1)) i = C.parent (C.rowCopy b s u+1) i) :
    Numeric.restrictedParent (C.row (C.rowCopy b s u)) (value C.toRowMountain newTop (C.rowCopy b s u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have ha := C.mountain.nested_succ u hP
  cases hQ : (C.mountain.row u).parent s with
  | none =>
      cases ha with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      by_cases hEqual : p = q
      · subst q
        exact Numeric.restrictedParent_eq_of_direct_parent
          (C.reconstructedRow newTop hPositive (C.rowCopy b s u+1)) (C.row (C.rowCopy b s u))
          (C.parent_succ_rowCopy hs hx hP b) (C.parent_rowCopy hx (by omega) hQ b)
      · have hQLive : u+1 ≤ C.mountain.height q := by
          rcases ancestor_parent_or_eq (C.mountain.row u) ha hQ with hPath | he
          · cases hPath with
            | direct hp => have := C.mountain.parent_source hp; omega
            | step _ hp => have := C.mountain.parent_source hp; omega
          · rw [← he]
            exact C.mountain.parent_endpoint hP
        have hQPos := value_pos C.mountain oldTop hOldPositive hQLive
        have hSparseP : Numeric.restrictedParent (C.mountain.row u)
            (value C.mountain oldTop (u+1)) s = some p := (hOldCanonical u s).trans hP
        obtain ⟨z, hZ, hZP, hLe⟩ := Numeric.restrictedParent_exists_blocker
          (C.mountain.row u) (value C.mountain oldTop (u+1)) hQ hSparseP hEqual hQPos
        have hForest : (Numeric.select (C.mountain.row u) (value C.mountain oldTop (u+1))).forest =
            C.mountain.row (u+1) := Numeric.parentForest_eq_of_parent_eq _ _ (hOldCanonical u)
        rw [hForest] at hZ
        rw [hOldCanonical u z] at hZP
        exact C.restrictedParent_bad_copy_of_blocker hRegular oldTop newTop hOldPositive hPositive
          hUpper hOldCanonical hs hx hQ hP hBad hZ hZP hLe b hHigher hPrefix

theorem restrictedParent_bad_copy_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop) {u s p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (b : Nat)
    (hHigher : ∀ r, C.rowCopy b s u+1 ≤ r → ∀ i, i ≤ C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row (C.rowCopy b s u))
        (value C.toRowMountain newTop (C.rowCopy b s u+1)) i = C.parent (C.rowCopy b s u+1) i) :
    Numeric.restrictedParent (C.row (C.rowCopy b s u)) (value C.toRowMountain newTop (C.rowCopy b s u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  apply C.restrictedParent_bad_copy (C.depthRegular_numeric base hBase hMountain)
    (Numeric.topValue base) newTop (fun c => Numeric.topValue_pos base (hBase c)) hPositive hUpper
    ?_ hs hx hP hBad b hHigher hPrefix
  intro r i
  rw [hMountain]
  exact restrictedParent_numeric_reconstruction base hBase r i

/-- Every inserted reference row (including its upper seam) has its direct
candidate as parent, so numerical recovery here needs no blocker induction. -/
theorem restrictedParent_reference (C : Context) (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    {s u : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hCone : C.InCone s)
    (b : Nat) (hu : C.floor ≤ u) (hTop : u+1 ≤ C.floor+b*C.rise) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = C.parent (u+1) (C.coordinates.parentCopy b s) := by
  obtain ⟨p, hp⟩ := C.mountain.parent_exists C.floor s (C.height_lt_of_inCone hCone hs)
  have hP : C.parent (u+1) (C.coordinates.parentCopy b s) = some (p+b*C.coordinates.length) := by
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
    change C.parent (u+1) (C.coordinates.encode s b) = _
    rw [C.parent_encode_reference hs hx hCone b (by omega) hTop, hp, Option.map_some]
  have hQ : C.parent u (C.coordinates.parentCopy b s) = some (p+b*C.coordinates.length) := by
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
    change C.parent u (C.coordinates.encode s b) = _
    rw [C.parent_encode_reference hs hx hCone b hu (by omega), hp, Option.map_some]
  rw [hP]
  exact Numeric.restrictedParent_eq_of_direct_parent (C.reconstructedRow newTop hPositive (u+1)) (C.row u) hP hQ

#print axioms parent_succ_rowCopy
#print axioms keyLE_succ_rowCopy
#print axioms bad_blocker_path
#print axioms restrictedParent_bad_copy_numeric
#print axioms restrictedParent_reference

end OneY.LowerCopy.Context
