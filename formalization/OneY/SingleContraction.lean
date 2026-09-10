import OneY.PseudoSelection
import OneY.SparseDepth
import OneY.LowerCopyPseudoSeam

/-! # Selecting through contractions to one retained root

The condition on a contracted column is supplied by the already restored
upper layer: every selected parent lies before the retained root. This
avoids any assumption that the lower numerical mountain is canonical.
-/

namespace OneY.Numeric

theorem select_eq_single_contraction (F G : ParentForest) (v : Nat → Nat)
    (hPositive : ∀ c, 0 < v c) (y : Nat)
    (hPrefix : ∀ c, c ≤ y → F.parent c = G.parent c)
    (hContract : ∀ c, F.parent c = G.parent c ∨
      (F.parent c = some y ∧ G.Ancestor y c ∧
        ∀ p, restrictedParent G v c = some p → p < y)) (c : Nat) :
    restrictedParent F v c = restrictedParent G v c := by
  have hFine : F.Refines G := by
    intro c p hp
    rcases hContract c with he | ⟨he, ha, _⟩
    · exact ParentForest.Ancestor.direct (he.symm.trans hp)
    · have hpy := Option.some.inj (hp.symm.trans he)
      subst p
      exact ha
  have hPrefixAnc : ∀ {a c}, c ≤ y → G.Ancestor a c → F.Ancestor a c := by
    intro a c hc ha
    induction ha with
    | direct hp => exact ParentForest.Ancestor.direct ((hPrefix _ hc).trans hp)
    | @step p c ha hp ih =>
        have hlt := G.parent_left hp
        exact ParentForest.Ancestor.step (ih (by omega)) ((hPrefix _ hc).trans hp)
  let S := (select G v).forest
  have hNS : ∀ c, ZeroY.Forest.nearestSmaller G.parent S.depth c = S.parent c :=
    select_depth_nearestSmaller G v (fun c hc => by have := hPositive c; omega)
  have hSelected : S.Refines F := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
        intro p hp
        have hAncPrefix : ∀ {a q}, q < c → S.Ancestor a q → F.Ancestor a q := by
          intro a q hq ha
          induction ha with
          | direct hp => exact ih _ hq hp
          | @step z q ha hp ihAnc =>
              have hlt := S.parent_left hp
              exact (ihAnc (by omega)).trans (ih _ hq hp)
        have hOld : G.Ancestor p c := ParentForest.ancestor_of_zeroY (restrictedParent_spec G v hp).1
        rcases hContract c with hEqual | ⟨hParent, hRoot, hGood⟩
        · cases hq : G.parent c with
          | none =>
              cases hOld with
              | direct hp => rw [hq] at hp; contradiction
              | step _ hp => rw [hq] at hp; contradiction
          | some q =>
              have hNewQ : F.parent c = some q := hEqual.trans hq
              rcases ZeroY.Forest.ancestor_eq_or_below_parent hq (ParentForest.ancestor_to_zeroY hOld) with he | ha
              · subst p
                exact ParentForest.Ancestor.direct hNewQ
              · have hpq := ZeroY.Forest.ancestor_lt G.parent_left ha
                have hSelectedAnc := ParentForest.ancestor_between_selected G S S.depth hNS
                  (ParentForest.Ancestor.direct hp) (ParentForest.Ancestor.direct hq) hpq
                exact (hAncPrefix (G.parent_left hq) hSelectedAnc).trans (ParentForest.Ancestor.direct hNewQ)
        · have hpy := hGood p hp
          have hpRoot : G.Ancestor p y := ParentForest.ancestor_of_zeroY
            (ZeroY.Forest.ancestor_of_common_target G.parent_left
              (ParentForest.ancestor_to_zeroY hOld) (ParentForest.ancestor_to_zeroY hRoot) hpy)
          exact (hPrefixAnc (Nat.le_refl _) hpRoot).trans (ParentForest.Ancestor.direct hParent)
  exact (select_parent_eq_of_refinements G F v hFine hSelected c).symm

#print axioms select_eq_single_contraction

end OneY.Numeric
