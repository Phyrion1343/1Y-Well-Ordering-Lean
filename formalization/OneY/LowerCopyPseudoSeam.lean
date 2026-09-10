import OneY.LowerCopyComparison

/-! # The low-row seam isolation used by pseudo-parent transport -/

namespace OneY.ParentForest

/-- Every intermediate candidate above a retained NS ancestor is itself a
descendant of that ancestor in the selected forest. The selected relation
is computed by NS, not an arbitrary refining subforest. -/
theorem ancestor_between_selected (F G : ParentForest) (v : Nat → Nat)
    (hNS : ∀ i, ZeroY.Forest.nearestSmaller F.parent v i = G.parent i)
    {a c z : Nat} (ha : G.Ancestor a c) (hz : F.Ancestor z c) (haz : a < z) :
    G.Ancestor a z := by
  have hMap : ZeroY.Forest.nearestSmaller F.parent v = G.parent := funext hNS
  induction ha generalizing z with
  | direct hp =>
      have ht := ZeroY.Forest.nearestSmaller_ancestor_of_between F.parent_left
        ((hNS _).trans hp) (ancestor_to_zeroY hz) haz
      rw [hMap] at ht
      exact ancestor_of_zeroY ht
  | @step p c ha hp ih =>
      have hPF : F.Ancestor p c := ancestor_of_zeroY
        ((ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mp ((hNS c).trans hp)).1
      by_cases hpz : p < z
      · have ht := ZeroY.Forest.nearestSmaller_ancestor_of_between F.parent_left
          ((hNS c).trans hp) (ancestor_to_zeroY hz) hpz
        rw [hMap] at ht
        exact ha.trans (ancestor_of_zeroY ht)
      · by_cases he : z = p
        · subst z
          exact ha
        · have hzp : F.Ancestor z p := ancestor_of_zeroY
            (ZeroY.Forest.ancestor_of_common_target F.parent_left
              (ancestor_to_zeroY hz) (ancestor_to_zeroY hPF) (by omega))
          exact ih hzp haz

end OneY.ParentForest

namespace OneY.LowerCopy.Context

/-- Along the old `P_(t-1)` path from the last column to the root, every
strictly intermediate column has height strictly greater than `t`.
The bound is `t`, not the possibly higher bad-root height. -/
theorem seam_intermediate_height (C : Context) (hRegular : C.DepthRegular)
    {t z : Nat} (hPositive : 0 < t) (hFloor : t ≤ C.floor)
    (hz : (C.mountain.row (t-1)).Ancestor z C.coordinates.x)
    (hAfter : C.coordinates.y < z) : t < C.mountain.height z := by
  have hRoot : (C.mountain.row C.floor).Ancestor C.coordinates.y C.coordinates.x := by
    rcases (C.mountain.rootAt_eq_iff_path (r := C.floor) (q := C.coordinates.y)
      (c := C.coordinates.x) rfl).mp C.last_root with ha | he
    · exact ha
    · have := C.coordinates.root_lt_last
      omega
  have htRoot := ParentForest.Refines.ancestor (C.mountain.refines_le hFloor) hRoot
  have he : t-1+1 = t := by omega
  have hNS : ∀ i, ZeroY.Forest.nearestSmaller (C.mountain.row (t-1)).parent
      (C.mountain.row t).depth i = (C.mountain.row t).parent i := by
    intro i
    simpa only [he] using hRegular (t-1) i
  have ha := ParentForest.ancestor_between_selected _ _ _ hNS htRoot hz hAfter
  cases ha with
  | direct hp => exact C.mountain.parent_source hp
  | step _ hp => exact C.mountain.parent_source hp

theorem seam_intermediate_height_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    {t z : Nat} (hPositive : 0 < t) (hFloor : t ≤ C.floor)
    (hz : (C.mountain.row (t-1)).Ancestor z C.coordinates.x)
    (hAfter : C.coordinates.y < z) : t < C.mountain.height z :=
  C.seam_intermediate_height (C.depthRegular_numeric base hBase hMountain) hPositive hFloor hz hAfter

#print axioms seam_intermediate_height
#print axioms seam_intermediate_height_numeric

end OneY.LowerCopy.Context
