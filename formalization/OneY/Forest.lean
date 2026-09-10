import Std

/-!
# Leftward parent forests and their computed roots

The root is a well-founded recursive computation on the column index. No
root map or root correctness theorem is part of the input structure.
-/

namespace OneY

structure ParentForest where
  parent : Nat → Option Nat
  parent_left : ∀ {c p : Nat}, parent c = some p → p < c

namespace ParentForest

def root (F : ParentForest) (c : Nat) : Nat :=
  match _hp : F.parent c with
  | none => c
  | some p => root F p
termination_by c
decreasing_by exact F.parent_left _hp

theorem root_of_parent_none (F : ParentForest) {c : Nat}
    (hp : F.parent c = none) : F.root c = c := by
  rw [root]
  split <;> simp_all

theorem root_of_parent_some (F : ParentForest) {c p : Nat}
    (hp : F.parent c = some p) : F.root c = F.root p := by
  rw [root]
  split <;> simp_all

theorem root_le (F : ParentForest) (c : Nat) : F.root c ≤ c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => rw [F.root_of_parent_none hp]
                exact Nat.le_refl c
      | some p =>
          rw [F.root_of_parent_some hp]
          exact Nat.le_trans (ih p (F.parent_left hp)) (Nat.le_of_lt (F.parent_left hp))

theorem parent_root (F : ParentForest) (c : Nat) : F.parent (F.root c) = none := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => simpa only [F.root_of_parent_none hp] using hp
      | some p =>
          rw [F.root_of_parent_some hp]
          exact ih p (F.parent_left hp)

theorem root_eq_self_iff (F : ParentForest) (c : Nat) :
    F.root c = c ↔ F.parent c = none := by
  constructor
  · intro h
    simpa only [h] using F.parent_root c
  · exact F.root_of_parent_none

theorem root_idempotent (F : ParentForest) (c : Nat) :
    F.root (F.root c) = F.root c :=
  F.root_of_parent_none (F.parent_root c)

theorem root_lt_of_parent_some (F : ParentForest) {c p : Nat}
    (hp : F.parent c = some p) : F.root c < c := by
  rw [F.root_of_parent_some hp]
  exact Nat.lt_of_le_of_lt (F.root_le p) (F.parent_left hp)

def depth (F : ParentForest) (c : Nat) : Nat :=
  match _hp : F.parent c with
  | none => 0
  | some p => depth F p + 1
termination_by c
decreasing_by exact F.parent_left _hp

theorem depth_of_parent_none (F : ParentForest) {c : Nat}
    (hp : F.parent c = none) : F.depth c = 0 := by
  rw [depth]
  split <;> simp_all

theorem depth_of_parent_some (F : ParentForest) {c p : Nat}
    (hp : F.parent c = some p) : F.depth c = F.depth p + 1 := by
  rw [depth]
  split <;> simp_all

theorem depth_le (F : ParentForest) (c : Nat) : F.depth c ≤ c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => rw [F.depth_of_parent_none hp]
                exact Nat.zero_le c
      | some p =>
          rw [F.depth_of_parent_some hp]
          have := ih p (F.parent_left hp)
          have := F.parent_left hp
          omega

theorem depth_zero_iff (F : ParentForest) (c : Nat) :
    F.depth c = 0 ↔ F.parent c = none := by
  constructor
  · intro hz
    cases hp : F.parent c with
    | none => rfl
    | some p => rw [F.depth_of_parent_some hp] at hz
                omega
  · exact F.depth_of_parent_none

/-- `Ancestor F a c` means that the strict parent chain from `c` reaches `a`. -/
inductive Ancestor (F : ParentForest) : Nat → Nat → Prop where
  | direct {a c : Nat} : F.parent c = some a → Ancestor F a c
  | step {a p c : Nat} : Ancestor F a p → F.parent c = some p → Ancestor F a c

theorem Ancestor.lt {F : ParentForest} {a c : Nat} (h : F.Ancestor a c) : a < c := by
  induction h with
  | direct hp => exact F.parent_left hp
  | step _ hp ih => exact Nat.lt_trans ih (F.parent_left hp)

theorem Ancestor.trans {F : ParentForest} {a b c : Nat}
    (hab : F.Ancestor a b) (hbc : F.Ancestor b c) : F.Ancestor a c := by
  induction hbc with
  | direct hp => exact Ancestor.step hab hp
  | step _ hp ih => exact Ancestor.step ih hp

theorem Ancestor.depth_lt {F : ParentForest} {a c : Nat}
    (h : F.Ancestor a c) : F.depth a < F.depth c := by
  induction h with
  | direct hp =>
      rw [F.depth_of_parent_some hp]
      omega
  | step _ hp ih =>
      rw [F.depth_of_parent_some hp]
      omega

theorem root_eq_of_ancestor {F : ParentForest} {a c : Nat}
    (h : F.Ancestor a c) : F.root c = F.root a := by
  induction h with
  | direct hp => exact F.root_of_parent_some hp
  | step _ hp ih => exact (F.root_of_parent_some hp).trans ih

theorem root_ancestor_or_eq (F : ParentForest) (c : Nat) :
    F.Ancestor (F.root c) c ∨ F.root c = c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => exact Or.inr (F.root_of_parent_none hp)
      | some p =>
          rw [F.root_of_parent_some hp]
          rcases ih p (F.parent_left hp) with h | h
          · exact Or.inl (Ancestor.step h hp)
          · apply Or.inl
            rw [h]
            exact Ancestor.direct hp

theorem root_unique (F : ParentForest) {r c : Nat}
    (hr : F.parent r = none) (hpath : F.Ancestor r c ∨ r = c) : F.root c = r := by
  rcases hpath with h | rfl
  · exact (root_eq_of_ancestor h).trans (F.root_of_parent_none hr)
  · exact F.root_of_parent_none hr

/-- A finer forest only selects ancestors of the coarser forest. -/
def Refines (fine coarse : ParentForest) : Prop :=
  ∀ {c p : Nat}, fine.parent c = some p → coarse.Ancestor p c

theorem refines_refl (F : ParentForest) : F.Refines F :=
  fun hp => Ancestor.direct hp

theorem Refines.ancestor {fine coarse : ParentForest} (h : fine.Refines coarse)
    {a c : Nat} (ha : fine.Ancestor a c) : coarse.Ancestor a c := by
  induction ha with
  | direct hp => exact h hp
  | step _ hp ih => exact ih.trans (h hp)

theorem Refines.trans {fine middle coarse : ParentForest}
    (hfm : fine.Refines middle) (hmc : middle.Refines coarse) : fine.Refines coarse :=
  fun hp => hmc.ancestor (hfm hp)

theorem Refines.root_eq_of_parent {fine coarse : ParentForest}
    (h : fine.Refines coarse) {c p : Nat} (hp : fine.parent c = some p) :
    coarse.root c = coarse.root p :=
  root_eq_of_ancestor (h hp)

theorem Refines.root_root {fine coarse : ParentForest} (h : fine.Refines coarse)
    (c : Nat) : coarse.root (fine.root c) = coarse.root c := by
  rcases fine.root_ancestor_or_eq c with ha | he
  · exact (root_eq_of_ancestor (h.ancestor ha)).symm
  · rw [he]

end ParentForest

end OneY

#print axioms OneY.ParentForest.root_le
#print axioms OneY.ParentForest.parent_root
#print axioms OneY.ParentForest.root_unique
#print axioms OneY.ParentForest.Refines.root_root
#print axioms OneY.ParentForest.depth_le
