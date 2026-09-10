import OneYTruth.BoundedEvaluation

/-!
# Bounded navigation through nested Kuratowski pairs

All existential witnesses are bounded by the pair and one of its members.
No union operation is added as a term, and no unbounded component witness is
hidden in the formula. These paths inspect literal syntax-code fields.
-/

namespace OneYTruth.CodedPaths

open Constructible Constructible.Delta0Formula

universe u

def Component : Bool → ZFSet.{u} → ZFSet.{u} → Prop
  | false, p, x => ∃ y, p = ZFSet.pair x y
  | true, p, x => ∃ y, p = ZFSet.pair y x

def componentEqAt {n : Nat} (right : Bool) (p x : Fin n) : Delta0Formula n :=
  .boundedEx p (.boundedEx (Fin.last n)
    (if right then kuratowskiPairEqAt p.castSucc.castSucc (Fin.last (n + 1)) x.castSucc.castSucc
      else kuratowskiPairEqAt p.castSucc.castSucc x.castSucc.castSucc (Fin.last (n + 1))))

theorem satisfies_componentEqAt {n : Nat} (right : Bool) (p x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (componentEqAt right p x) s ↔ Component right (s p) (s x) := by
  cases right <;> simp only [componentEqAt, Bool.false_eq_true, if_false, if_true,
    Satisfies, satisfies_kuratowskiPairEqAt, snoc_last, snoc_castSucc, Component]
  · constructor
    · rintro ⟨box, _, y, _, h⟩
      exact ⟨y, h⟩
    · rintro ⟨y, h⟩
      refine ⟨{s x, y}, ?_, y, ?_, h⟩
      · rw [h]
        simp [ZFSet.pair]
      · simp
  · constructor
    · rintro ⟨box, _, y, _, h⟩
      exact ⟨y, h⟩
    · rintro ⟨y, h⟩
      refine ⟨{y, s x}, ?_, y, ?_, h⟩
      · rw [h]
        simp [ZFSet.pair]
      · simp

theorem component_bounded {right : Bool} {p x : ZFSet.{u}} (h : Component right p x) :
    ∃ box ∈ p, x ∈ box := by
  cases right with
  | false =>
    obtain ⟨y, rfl⟩ := h
    exact ⟨{x, y}, by simp [ZFSet.pair], by simp⟩
  | true =>
    obtain ⟨y, rfl⟩ := h
    exact ⟨{y, x}, by simp [ZFSet.pair], by simp⟩

@[simp]
theorem component_pair {right : Bool} {a b x : ZFSet.{u}} :
    Component right (ZFSet.pair a b) x ↔ x = (if right then b else a) := by
  cases right <;> simp [Component, ZFSet.pair_inj, eq_comm]

def Follows : List Bool → ZFSet.{u} → ZFSet.{u} → Prop
  | [], p, x => p = x
  | right :: rest, p, x => ∃ y, Component right p y ∧ Follows rest y x

@[simp]
theorem follows_pair {right : Bool} {rest : List Bool} {a b x : ZFSet.{u}} :
    Follows (right :: rest) (ZFSet.pair a b) x ↔ Follows rest (if right then b else a) x := by
  simp only [Follows, component_pair, exists_eq_left]

/-- The value reached along the path belongs to the set at coordinate b. -/
def pathMemAt : (path : List Bool) → {n : Nat} → Fin n → Fin n → Delta0Formula n
  | [], _, p, b => .mem p b
  | right :: rest, n, p, b =>
    .boundedEx p (.boundedEx (Fin.last n)
      (.conj (componentEqAt right p.castSucc.castSucc (Fin.last (n + 1)))
        (pathMemAt rest (Fin.last (n + 1)) b.castSucc.castSucc)))

theorem satisfies_pathMemAt (path : List Bool) {n : Nat} (p b : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (pathMemAt path p b) s ↔
      ∃ x, Follows path (s p) x ∧ x ∈ s b := by
  induction path generalizing n with
  | nil => simp [pathMemAt, Satisfies, Follows, ZFMem]
  | cons right rest ih =>
    simp only [pathMemAt, Satisfies, satisfies_componentEqAt, ih,
      snoc_last, snoc_castSucc]
    constructor
    · rintro ⟨box, _, x, _, hx, z, hpath, hz⟩
      exact ⟨z, ⟨x, hx, hpath⟩, hz⟩
    · rintro ⟨z, ⟨x, hx, hpath⟩, hz⟩
      obtain ⟨box, hbox, hxb⟩ := component_bounded hx
      exact ⟨box, hbox, x, hxb, hx, z, hpath, hz⟩

end OneYTruth.CodedPaths
