import OneY.Reconstruction

/-! # Structurally recursive evaluation of the proved reconstruction function

The column bound makes evaluation independent of reduction of well-founded
recursion proofs. The equality below connects it to the original definition.
-/

namespace OneY.Reconstruction

open RootGeometry

def valueFuel (M : RowMountain) (top : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, r, c =>
      if r ≤ M.height c then
        top c + ((List.range' r (M.height c-r)).map fun u =>
          match (M.row u).parent c with
          | none => 0
          | some p => valueFuel M top fuel u p).sum
      else 0

theorem valueFuel_eq (M : RowMountain) (top : Nat → Nat) (fuel : Nat) :
    ∀ r c, c < fuel → valueFuel M top fuel r c = value M top r c := by
  induction fuel with
  | zero => intro r c hc; omega
  | succ fuel ih =>
      intro r c hc
      rw [valueFuel, value_eq]
      by_cases hr : r ≤ M.height c
      · simp only [hr, ↓reduceIte]
        congr 2
        apply List.map_congr_left
        intro u hu
        unfold parentValue
        cases hp : (M.row u).parent c with
        | none => rfl
        | some p =>
            have hp' := (M.row u).parent_left hp
            exact ih u p (by omega)
      · simp [hr]

theorem value_eq_compute (M : RowMountain) (top : Nat → Nat) (r c : Nat) :
    value M top r c = valueFuel M top (c+1) r c :=
  (valueFuel_eq M top (c+1) r c (by omega)).symm

end OneY.Reconstruction

#print axioms OneY.Reconstruction.value_eq_compute
