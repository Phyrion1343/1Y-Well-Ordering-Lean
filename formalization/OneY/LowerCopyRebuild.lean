import OneY.LowerCopyTransport
import OneY.LowerCopyTopForest
import OneY.OrdinaryCopyExtraction
import OneY.PseudoSelection

/-! # Rebuilding a lower copy from its computed values

The explicit hypotheses are prefix top equality, upper B/C, and the
pseudo-top bound. Every current-layer NS equation, height and extraction
equation below is proved from those hypotheses.
-/

namespace OneY.LowerCopy.Context

open Reconstruction

def copiedBase (C : Context) (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c) : Numeric.Row :=
  numericRow C.toRowMountain newTop hPositive 0

theorem copiedBase_positive (C : Context) (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (c : Nat) : 0 < (C.copiedBase newTop hPositive).value c :=
  value_pos _ _ hPositive (Nat.zero_le _)

section Recovery

variable (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hBound : PseudoTopBound C.toRowMountain newTop)

include hMountain hPrefixTop hFixed hUpper hBound

theorem copiedBase_rows (r : Nat) :
    Numeric.rows (C.copiedBase newTop hPositive) r = numericRow C.toRowMountain newTop hPositive r := by
  simpa only [copiedBase, Nat.zero_add] using
    numericRow_rows C.toRowMountain newTop hPositive 0
      (fun u _ => C.restrictedParent_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound u) r

theorem copiedBase_height (c : Nat) :
    Numeric.height (C.copiedBase newTop hPositive) c = C.height c := by
  have hLive : ∀ r, 0 < (Numeric.rows (C.copiedBase newTop hPositive) r).value c ↔ r ≤ C.height c := by
    intro r
    rw [C.copiedBase_rows base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound r]
    exact value_pos_iff C.toRowMountain newTop hPositive r c
  apply Nat.le_antisymm
  · exact (hLive _).mp (Numeric.height_live _ (C.copiedBase_positive newTop hPositive c))
  · exact (Numeric.live_iff_le_height _ (C.copiedBase_positive newTop hPositive c) _).mp
      ((hLive _).mpr (Nat.le_refl _))

theorem copiedBase_topValue (c : Nat) : Numeric.topValue (C.copiedBase newTop hPositive) c = newTop c :=
  numericRow_topValue C.toRowMountain newTop hPositive 0
    (fun u _ => C.restrictedParent_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound u)
    (Nat.zero_le _)

theorem copiedBase_mountain :
    Numeric.mountain (C.copiedBase newTop hPositive) (C.copiedBase_positive newTop hPositive) = C.toRowMountain := by
  apply RootGeometry.RowMountain.ext_height_parents
  · funext c
    exact C.copiedBase_height base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound c
  · intro r
    funext c
    change (Numeric.rows (C.copiedBase newTop hPositive) r).forest.parent c = _
    rw [C.copiedBase_rows base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound r]
    rfl

/-- The extraction is calculated in the transported strict-height forest.
Identifying this with a separately expanded upper layer remains a separate
cross-layer transport obligation. -/
theorem copiedBase_rawExtract :
    Numeric.rawExtract (C.copiedBase newTop hPositive) (C.copiedBase_positive newTop hPositive) =
      Numeric.select (FrameCopy.forest C.coordinates C.mountain.topForest) newTop := by
  have hTop : Numeric.topValue (C.copiedBase newTop hPositive) = newTop :=
    funext (C.copiedBase_topValue base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound)
  apply Numeric.Row.ext_values_parents
  · exact hTop
  · funext c
    rw [Numeric.rawExtract_parent_eq_topForest,
      C.copiedBase_mountain base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound,
      hTop, C.topForest_eq_frameCopy]

end Recovery

theorem copiedBase_rootsOne (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop) :
    (C.copiedBase newTop hPositive).RootsOne := by
  intro c hp
  change C.parent 0 c = none at hp
  change value C.toRowMountain newTop 0 c = 1
  by_cases hc : c < C.coordinates.x
  · rw [← C.value_original_prefix_eq (Numeric.topValue base) newTop hPrefixTop hc 0, hMountain, value_numeric_base]
    rw [C.parent_original (Nat.le_of_lt hc), hMountain] at hp
    exact hRoots c hp
  · have hs := C.coordinates.source_bounds c
    have he : C.coordinates.parentCopy (C.coordinates.block c) (C.coordinates.source c) = c := by
      rw [C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)]
      exact C.coordinates.encode_coordinates (by have := C.coordinates.root_lt_last; omega)
    have hParent := C.parent_zero_parentCopy hs.1 hs.2 (C.coordinates.block c)
    rw [he, hp] at hParent
    have hOld : (C.mountain.row 0).parent (C.coordinates.source c) = none := by
      cases ht : (C.mountain.row 0).parent (C.coordinates.source c) with
      | none => rfl
      | some p => simp only [ht, Option.map_some] at hParent; contradiction
    have hv := C.value_bottom_none_eq_one base hBase hRoots hMountain newTop hFixed hs.1 hs.2 hOld (C.coordinates.block c)
    simpa only [he] using hv

#print axioms copiedBase_mountain
#print axioms copiedBase_rawExtract
#print axioms copiedBase_rootsOne

end OneY.LowerCopy.Context
