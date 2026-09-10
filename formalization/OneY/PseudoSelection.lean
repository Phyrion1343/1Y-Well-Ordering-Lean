import OneY.PseudoCollapse
import OneY.ExtractionGeometry
import ZeroY.Forest.Blocker

/-!
# Replacing the pseudo-parent forest by the computed top forest

Equal-height pseudo-ancestor segments have antitone top values. Nearest
smaller top-value selection therefore keeps only the strict height records,
which are exactly the computed vertical chain of row component roots.
-/

namespace OneY.ParentForest

theorem nearestSmaller_parent_equal (F : ParentForest) (v : Nat → Nat)
    {c p : Nat} (hp : F.parent c = some p) (heq : v p = v c) :
    (F.nearestSmaller v).parent c = (F.nearestSmaller v).parent p := by
  change ZeroY.Forest.nearestSmaller F.parent v c =
    ZeroY.Forest.nearestSmaller F.parent v p
  cases hn : ZeroY.Forest.nearestSmaller F.parent v p with
  | none =>
      apply (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mpr
      intro q ha
      rcases ZeroY.Forest.ancestor_eq_or_below_parent hp ha with rfl | hq
      · omega
      · have h := (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mp hn q hq
        omega
  | some a =>
      obtain ⟨ha, hv, hmax⟩ :=
        (ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mp hn
      apply (ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mpr
      refine ⟨ZeroY.Forest.ancestor_trans (Relation.TransGen.single hp) ha,
        by omega, ?_⟩
      intro q hq hvq
      rcases ZeroY.Forest.ancestor_eq_or_below_parent hp hq with rfl | hq'
      · omega
      · exact hmax q hq' (by omega)

theorem nearestSmaller_parent_none (F : ParentForest) (v : Nat → Nat)
    {c : Nat} (hp : F.parent c = none) :
    (F.nearestSmaller v).parent c = none := by
  apply (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mpr
  intro q ha
  have h := ancestor_of_zeroY ha
  cases h with
  | direct hq => rw [hp] at hq; contradiction
  | step _ hq => rw [hp] at hq; contradiction

end OneY.ParentForest

namespace OneY.Pseudo

open RootGeometry

theorem nearestSmaller_height_eq_lowerParent (M : RowMountain) (c : Nat) :
    ((forest M).nearestSmaller M.height).parent c = lowerParent M c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : parent M c with
      | none =>
          rw [lowerParent_of_none M hp]
          exact (forest M).nearestSmaller_parent_none M.height hp
      | some p =>
          rw [lowerParent_of_some M hp]
          by_cases hlt : M.height p < M.height c
          · rw [if_pos hlt]
            exact ZeroY.Forest.nearestSmaller_eq_of_direct
              (forest M).parent_left hp hlt
          · rw [if_neg hlt]
            have hh := parent_height M hp
            rw [(forest M).nearestSmaller_parent_equal M.height hp (by omega)]
            exact ih p (parent_left M hp)

theorem nearestSmaller_height_eq_topForest (M : RowMountain) (c : Nat) :
    ((forest M).nearestSmaller M.height).parent c = M.topForest.parent c := by
  rw [nearestSmaller_height_eq_lowerParent, lowerParent_eq_topForest]

theorem topForest_refines (M : RowMountain) : M.topForest.Refines (forest M) := by
  intro c p hp
  rw [← nearestSmaller_height_eq_topForest] at hp
  exact (forest M).nearestSmaller_refines M.height hp

end OneY.Pseudo

namespace OneY.Numeric

/-- A candidate forest may be contracted whenever every actually selected
edge still lies in the contracted forest. No unselected candidate needs
to be retained. -/
theorem select_parent_eq_of_refinements (coarse fine : ParentForest)
    (v : Nat → Nat) (hFine : fine.Refines coarse)
    (hSelected : (select coarse v).forest.Refines fine) (c : Nat) :
    (select coarse v).forest.parent c = (select fine v).forest.parent c := by
  cases hp : (select coarse v).forest.parent c with
  | none =>
      symm
      apply (restrictedParent_none_iff fine v c).mpr
      intro p ha hv
      exact (restrictedParent_none_iff coarse v c).mp hp p
        (hFine.ancestor ha) hv
  | some p =>
      symm
      obtain ⟨_, hvp, hvc, hmax⟩ :=
        (restrictedParent_some_iff coarse v c p).mp hp
      apply (restrictedParent_some_iff fine v c p).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (hSelected hp), hvp, hvc, ?_⟩
      intro q hq hqv hqc
      exact hmax q (ParentForest.ancestor_to_zeroY
        (hFine.ancestor (ParentForest.ancestor_of_zeroY hq))) hqv hqc

/-- The sole numerical condition needed for contracting the pseudo forest:
top values are antitone on its equal-height ancestor segments. -/
theorem pseudo_select_refines_topForest
    (M : RootGeometry.RowMountain) (v : Nat → Nat) (hpos : ∀ c, 0 < v c)
    (hanti : ∀ {p c}, (Pseudo.forest M).Ancestor p c →
      M.height p = M.height c → v c ≤ v p) :
    (select (Pseudo.forest M) v).forest.Refines M.topForest := by
  intro c p hp
  obtain ⟨hap, hvp, hvc, hmax⟩ :=
    (restrictedParent_some_iff (Pseudo.forest M) v c p).mp hp
  have hpc := ParentForest.ancestor_of_zeroY hap
  have hheight : M.height p < M.height c := by
    have hle := Pseudo.ancestor_height_le M hpc
    by_cases heq : M.height p = M.height c
    · have hbound := hanti hpc heq
      omega
    · omega
  have hrecord : ∀ q, ZeroY.Forest.Ancestor (Pseudo.forest M).parent c q →
      p < q → M.height p < M.height q := by
    intro q hq hpq
    have hpqAnc := ParentForest.ancestor_of_zeroY
      (ZeroY.Forest.ancestor_of_common_target (Pseudo.forest M).parent_left hap hq hpq)
    have hle := Pseudo.ancestor_height_le M hpqAnc
    by_cases heq : M.height p = M.height q
    · have hbound := hanti hpqAnc heq
      have hqv : v q < v c := by omega
      have horder := hmax q hq (hpos q) hqv
      omega
    · omega
  have hrecordAnc := ZeroY.Forest.ancestor_of_record_minimum
    (Pseudo.forest M).parent_left hap hheight hrecord
  apply ParentForest.ancestor_of_zeroY
  exact ZeroY.Forest.ancestor_transfer_prefix
    (ZeroY.Forest.nearestSmaller_leftward (Pseudo.forest M).parent M.height)
    (Nat.lt_succ_self c)
    (fun i _ => Pseudo.nearestSmaller_height_eq_topForest M i) hrecordAnc

theorem pseudo_select_parent_eq_topForest
    (M : RootGeometry.RowMountain) (v : Nat → Nat) (hpos : ∀ c, 0 < v c)
    (hanti : ∀ {p c}, (Pseudo.forest M).Ancestor p c →
      M.height p = M.height c → v c ≤ v p) (c : Nat) :
    (select (Pseudo.forest M) v).forest.parent c =
      (select M.topForest v).forest.parent c :=
  select_parent_eq_of_refinements (Pseudo.forest M) M.topForest v
    (Pseudo.topForest_refines M) (pseudo_select_refines_topForest M v hpos hanti) c

theorem rawExtract_refines_topForest (base : Row) (hpos : ∀ c, 0 < base.value c) :
    (rawExtract base hpos).forest.Refines (mountain base hpos).topForest := by
  intro c p hp
  exact pseudo_select_refines_topForest (mountain base hpos) (topValue base)
    (fun q => topValue_pos base (hpos q))
    (fun ha heq => topValue_le_of_same_height_pseudo_ancestor base hpos ha heq) hp

theorem rawExtract_parent_eq_topForest (base : Row) (hpos : ∀ c, 0 < base.value c)
    (c : Nat) :
    (rawExtract base hpos).forest.parent c =
      (select (mountain base hpos).topForest (topValue base)).forest.parent c :=
  pseudo_select_parent_eq_topForest (mountain base hpos) (topValue base)
    (fun q => topValue_pos base (hpos q))
    (fun ha heq => topValue_le_of_same_height_pseudo_ancestor base hpos ha heq) c

end OneY.Numeric

#print axioms OneY.Pseudo.nearestSmaller_height_eq_topForest
#print axioms OneY.Pseudo.topForest_refines
#print axioms OneY.Numeric.pseudo_select_parent_eq_topForest
#print axioms OneY.Numeric.rawExtract_refines_topForest
#print axioms OneY.Numeric.rawExtract_parent_eq_topForest
