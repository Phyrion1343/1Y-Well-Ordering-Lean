import OneY.LowerCopyBadBlocker
import OneY.ReconstructionTop

/-! # Conditional finite-row canonicality of the computed lower copy

The external conditions are the upper layer's B/C value comparisons and its
equal-height pseudo-parent bound. No current-layer canonicality is a field.
-/

namespace OneY.LowerCopy.Context

open Reconstruction

theorem restrictedParent_source_next_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop) {u s p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row (u+1)).parent s = some p) (b : Nat)
    (hHigher : ∀ r, C.rowCopy b s u+1 ≤ r → ∀ i, i ≤ C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row (C.rowCopy b s u))
        (value C.toRowMountain newTop (C.rowCopy b s u+1)) i = C.parent (C.rowCopy b s u+1) i) :
    Numeric.restrictedParent (C.row (C.rowCopy b s u)) (value C.toRowMountain newTop (C.rowCopy b s u+1))
      (C.coordinates.parentCopy b s) = C.parent (C.rowCopy b s u+1) (C.coordinates.parentCopy b s) := by
  rw [C.parent_succ_rowCopy hs hx hP b]
  by_cases hBad : C.coordinates.y ≤ p
  · exact C.restrictedParent_bad_copy_numeric base hBase hMountain newTop hPositive hUpper
      hs hx hP hBad b hHigher hPrefix
  · have hGood : p < C.coordinates.y := by omega
    have hOut := C.not_inCone_of_good_parent hs hP hGood
    have hxStrict : s < C.coordinates.x := by
      by_cases he : s = C.coordinates.x
      · subst s; exact False.elim (hOut C.last_inCone)
      · omega
    rw [C.rowCopy_outside hOut] at hPrefix ⊢
    rw [C.coordinates.parentCopy_good b hGood]
    exact C.restrictedParent_good_copy_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed
      hs hxStrict hP hGood b hPrefix

theorem restrictedParent_copied_some_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop) {u s p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat)
    (hP : C.parent (u+1) (C.coordinates.parentCopy b s) = some p)
    (hHigher : ∀ r, u+1 ≤ r → ∀ i, i ≤ C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) (C.coordinates.parentCopy b s) =
      C.parent (u+1) (C.coordinates.parentCopy b s) := by
  have hLive := C.parent_source hP
  rw [C.height_parentCopy hx b] at hLive
  have hOrdinary : ∀ v, v+1 < C.mountain.height s → C.rowCopy b s v = u →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) (C.coordinates.parentCopy b s) =
        C.parent (u+1) (C.coordinates.parentCopy b s) := by
    intro v hv he
    obtain ⟨q, hq⟩ := C.mountain.parent_exists (v+1) s hv
    have ht := C.restrictedParent_source_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper
      hs hx hq b (by simpa only [he] using hHigher) (by simpa only [he] using hPrefix)
    simpa only [he] using ht
  by_cases hCone : C.InCone s
  · rw [if_pos hCone] at hLive
    by_cases hLow : u < C.floor
    · exact hOrdinary u (by have := C.height_lt_of_inCone hCone hs; omega) (C.rowCopy_low hLow b s)
    · have hu : C.floor ≤ u := by omega
      by_cases hFill : u+1 ≤ C.floor+b*C.rise
      · exact C.restrictedParent_reference newTop hPositive hs hx hCone b hu hFill
      · have he : u-b*C.rise+b*C.rise = u := by omega
        apply hOrdinary (u-b*C.rise) (by omega)
        rw [rowCopy, if_pos ⟨hCone, by omega⟩, he]
  · rw [if_neg hCone] at hLive
    exact hOrdinary u hLive (C.rowCopy_outside hCone b u)

theorem restrictedParent_original_prefix_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    {c : Nat} (hc : c < C.coordinates.x) (u : Nat) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) c = C.parent (u+1) c := by
  rw [Numeric.restrictedParent_agreesBelow (C.row u) (C.mountain.row u)
    (value C.toRowMountain newTop (u+1)) (value C.mountain (Numeric.topValue base) (u+1)) C.coordinates.x
    (fun q hq => C.parent_original (Nat.le_of_lt hq))
    (fun q hq => (C.value_original_prefix_eq (Numeric.topValue base) newTop hPrefixTop hq (u+1)).symm) hc,
    C.parent_original (Nat.le_of_lt hc), hMountain]
  exact restrictedParent_numeric_reconstruction base hBase u c

/-- One finite row/column induction step, for every source and all three
physical copy regions. Higher rows are required only through the target. -/
theorem restrictedParent_next_of_higher_prefix (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hBound : PseudoTopBound C.toRowMountain newTop) (u c : Nat)
    (hHigher : ∀ r, u+1 ≤ r → ∀ i, i ≤ c →
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < c →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) c = C.parent (u+1) c := by
  by_cases hOriginal : c < C.coordinates.x
  · exact C.restrictedParent_original_prefix_numeric base hBase hMountain newTop hPrefixTop hOriginal u
  · cases hp : C.parent (u+1) c with
    | none =>
        have hHeight := (C.parent_none_iff _ _).mp hp
        by_cases hTop : C.height c = u+1
        · exact restrictedParent_top_none C.toRowMountain newTop hPositive hBound hTop hPrefix
        · apply (Numeric.restrictedParent_none_iff (C.row u) (value C.toRowMountain newTop (u+1)) c).mpr
          intro q _ _
          rw [value_absent C.toRowMountain newTop (by change C.height c < u+1; omega)]
          exact Nat.zero_le _
    | some p =>
        have hAfter : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
        have hs := C.coordinates.source_bounds c
        have he : C.coordinates.parentCopy (C.coordinates.block c) (C.coordinates.source c) = c := by
          rw [C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)]
          exact C.coordinates.encode_coordinates hAfter
        have ht := C.restrictedParent_copied_some_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper
          hs.1 hs.2 (C.coordinates.block c) (by simpa only [he] using hp)
          (by simpa only [he] using hHigher) (by simpa only [he] using hPrefix)
        simpa only [he, hp] using ht

theorem finite_height_bound (M : RootGeometry.RowMountain) (n : Nat) :
    ∃ bound, ∀ c, c < n → M.height c ≤ bound := by
  induction n with
  | zero => exact ⟨0, fun c hc => by omega⟩
  | succ n ih =>
      obtain ⟨bound, hBound⟩ := ih
      refine ⟨bound+M.height n, ?_⟩
      intro c hc
      by_cases hBefore : c < n
      · have := hBound c hBefore; omega
      · have he : c = n := by omega
        rw [he]
        omega

/-- The higher-row and strict-left-prefix induction hypotheses are discharged
here, using a computed finite height bound on each column prefix. -/
theorem restrictedParent_next_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hBound : PseudoTopBound C.toRowMountain newTop) (u c : Nat) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) c = C.parent (u+1) c := by
  have all : ∀ n bound, (∀ i, i < n → C.height i ≤ bound) →
      ∀ fuel u, bound ≤ u+fuel → ∀ c, c < n →
        Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) c = C.parent (u+1) c := by
    intro n bound hHeight fuel
    induction fuel with
    | zero =>
        intro u hu c hc
        have hh := hHeight c hc
        have hp : C.parent (u+1) c = none := (C.parent_none_iff _ _).mpr (by omega)
        rw [hp]
        apply (Numeric.restrictedParent_none_iff (C.row u) (value C.toRowMountain newTop (u+1)) c).mpr
        intro q _ _
        rw [value_absent C.toRowMountain newTop (by change C.height c < u+1; omega)]
        exact Nat.zero_le _
    | succ fuel ih =>
        intro u hu c
        induction c using Nat.strongRecOn with
        | ind c ihCol =>
            intro hc
            apply C.restrictedParent_next_of_higher_prefix base hBase hMountain newTop hPositive
              hPrefixTop hFixed hUpper hBound u c
            · intro r hr i hi
              exact ih r (by omega) i (by omega)
            · intro i hi
              exact ihCol i hi (by omega)
  obtain ⟨bound, hHeight⟩ := finite_height_bound C.toRowMountain (c+1)
  exact all (c+1) bound hHeight bound u (by omega) c (by omega)

theorem restrictedParent_next_numeric_of_extracted (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hDecrease : ExtractedHeightDecrease C.toRowMountain newTop) (u c : Nat) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) c = C.parent (u+1) c :=
  C.restrictedParent_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper
    (pseudoTopBound_of_extractedHeightDecrease C.toRowMountain newTop hPositive hDecrease) u c

#print axioms restrictedParent_source_next_numeric
#print axioms restrictedParent_copied_some_numeric
#print axioms restrictedParent_next_of_higher_prefix
#print axioms restrictedParent_next_numeric
#print axioms restrictedParent_next_numeric_of_extracted

end OneY.LowerCopy.Context
