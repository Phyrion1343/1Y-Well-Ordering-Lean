import OneYTruth.CodedPaths

/-! Literal code-field equality with only bounded component witnesses. -/

namespace OneYTruth.CodedPaths

open Constructible Constructible.Delta0Formula

universe u

theorem componentRight_and_leftMem_iff (p tail U : ZFSet.{u}) :
    Component true p tail ∧ (∃ head, Component false p head ∧ head ∈ U) ↔
      ∃ head ∈ U, p = ZFSet.pair head tail := by
  constructor
  · rintro ⟨⟨head, hp⟩, a, ha, haU⟩
    have heq : a = head := component_pair.mp (hp ▸ ha)
    exact ⟨head, heq ▸ haU, hp⟩
  · rintro ⟨head, hhead, hp⟩
    exact ⟨⟨head, hp⟩, head, ⟨tail, hp⟩, hhead⟩

def pathEqAt : (path : List Bool) → {n : Nat} → Fin n → Fin n → Delta0Formula n
  | [], _, p, x => .eq p x
  | right :: rest, n, p, x =>
    .boundedEx p (.boundedEx (Fin.last n)
      (.conj (componentEqAt right p.castSucc.castSucc (Fin.last (n + 1)))
        (pathEqAt rest (Fin.last (n + 1)) x.castSucc.castSucc)))

theorem satisfies_pathEqAt (path : List Bool) {n : Nat} (p x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (pathEqAt path p x) s ↔ Follows path (s p) (s x) := by
  induction path generalizing n with
  | nil => rfl
  | cons right rest ih =>
    simp only [pathEqAt, Satisfies, satisfies_componentEqAt, ih,
      snoc_last, snoc_castSucc, Follows]
    constructor
    · rintro ⟨box, _, y, _, hy, hpath⟩
      exact ⟨y, hy, hpath⟩
    · rintro ⟨y, hy, hpath⟩
      obtain ⟨box, hbox, hybox⟩ := component_bounded hy
      exact ⟨box, hbox, y, hybox, hy, hpath⟩

def pathsEqualAt : (left right : List Bool) → {n : Nat} → Fin n → Fin n → Delta0Formula n
  | [], right, _, p, q => pathEqAt right q p
  | step :: rest, right, n, p, q =>
    .boundedEx p (.boundedEx (Fin.last n)
      (.conj (componentEqAt step p.castSucc.castSucc (Fin.last (n + 1)))
        (pathsEqualAt rest right (Fin.last (n + 1)) q.castSucc.castSucc)))

theorem satisfies_pathsEqualAt (left right : List Bool) {n : Nat} (p q : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (pathsEqualAt left right p q) s ↔
      ∃ x, Follows left (s p) x ∧ Follows right (s q) x := by
  induction left generalizing n with
  | nil => simp [pathsEqualAt, satisfies_pathEqAt, Follows]
  | cons step rest ih =>
    simp only [pathsEqualAt, Satisfies, satisfies_componentEqAt, ih,
      snoc_last, snoc_castSucc]
    constructor
    · rintro ⟨box, _, y, _, hy, x, hleft, hright⟩
      exact ⟨x, ⟨y, hy, hleft⟩, hright⟩
    · rintro ⟨x, ⟨y, hy, hleft⟩, hright⟩
      obtain ⟨box, hbox, hybox⟩ := component_bounded hy
      exact ⟨box, hbox, y, hybox, hy, x, hleft, hright⟩

end OneYTruth.CodedPaths
