import OneY.Forest
import ZeroY.Forest.Stack

/-!
# Interoperability with the existing ZeroY forest library

ZeroY writes `Ancestor parent child ancestor`; OneY writes
`ParentForest.Ancestor ancestor child`. The conversion is proved in both
directions, with no additional forest assumption.
-/

namespace OneY.ParentForest

theorem ancestor_of_zeroY {F : OneY.ParentForest} {a c : Nat}
    (h : ZeroY.Forest.Ancestor F.parent c a) : F.Ancestor a c := by
  induction h with
  | single hp => exact Ancestor.direct hp
  | tail _ hp ih => exact (Ancestor.direct hp).trans ih

theorem ancestor_to_zeroY {F : OneY.ParentForest} {a c : Nat}
    (h : F.Ancestor a c) : ZeroY.Forest.Ancestor F.parent c a := by
  induction h with
  | direct hp => exact Relation.TransGen.single hp
  | step _ hp ih => exact Relation.TransGen.trans (Relation.TransGen.single hp) ih

theorem ancestor_iff_zeroY (F : OneY.ParentForest) (a c : Nat) :
    F.Ancestor a c ↔ ZeroY.Forest.Ancestor F.parent c a :=
  ⟨ancestor_to_zeroY, ancestor_of_zeroY⟩

def nearestSmaller (F : OneY.ParentForest) (value : Nat → Nat) : OneY.ParentForest where
  parent := ZeroY.Forest.nearestSmaller F.parent value
  parent_left := ZeroY.Forest.nearestSmaller_leftward F.parent value

theorem nearestSmaller_refines (F : OneY.ParentForest) (value : Nat → Nat) :
    (F.nearestSmaller value).Refines F := by
  intro c p hp
  have h : ZeroY.Forest.nearestSmaller F.parent value c = some p := hp
  exact ancestor_of_zeroY
    ((ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mp h).1

theorem root_nearestSmaller_root (F : OneY.ParentForest) (value : Nat → Nat) (c : Nat) :
    F.root ((F.nearestSmaller value).root c) = F.root c :=
  Refines.root_root (F.nearestSmaller_refines value) c

end OneY.ParentForest

#print axioms OneY.ParentForest.ancestor_iff_zeroY
#print axioms OneY.ParentForest.nearestSmaller_refines
#print axioms OneY.ParentForest.root_nearestSmaller_root
