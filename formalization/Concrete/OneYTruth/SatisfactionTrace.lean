import OneYTruth.AuxiliarySetRestriction
import OneYTruth.SatisfactionSet

/-!
# Full satisfaction traces on a transitive smaller domain

A coded assignment internal to a transitive set has all its entries in
that set. Formula elementarity therefore preserves satisfaction even on
arbitrary set codes, including invalid codes, not just chosen syntax nodes.
-/

namespace OneYTruth

open Constructible Constructible.FiniteSequenceZF FormulaCode

universe u v

theorem pair_components_mem {V a b : ZFSet.{u}} (hV : V.IsTransitive)
    (hp : ZFSet.pair a b ∈ V) : a ∈ V ∧ b ∈ V := by
  have hab : ({a, b} : ZFSet.{u}) ∈ V := hV.mem_trans (by simp [ZFSet.pair]) hp
  exact ⟨hV.mem_trans (by simp) hab, hV.mem_trans (by simp) hab⟩

theorem listCode_entries_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (xs : List ZFSet.{u}) (hxs : listCode xs ∈ V) : ∀ x ∈ xs, x ∈ V := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      obtain ⟨ha, htail⟩ := pair_components_mem hV hxs
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih htail x hx

theorem sequenceCode_entries_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (xs : List ZFSet.{u}) (hxs : sequenceCode xs ∈ V) : ∀ x ∈ xs, x ∈ V :=
  listCode_entries_mem hV xs (pair_components_mem hV hxs).2

theorem assignmentCode_entries_mem {U V : ZFSet.{u}} (hV : V.IsTransitive)
    {n : Nat} (xs : Fin n → ZFCarrier U) (hxs : assignmentCode xs ∈ V) :
    ∀ i, (xs i).val ∈ V := by
  intro i
  exact sequenceCode_entries_mem hV _ hxs _
    (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem assignmentCode_eq_of_values_eq {U V : ZFSet.{u}} {n : Nat}
    (xs : Fin n → ZFCarrier U) (ys : Fin n → ZFCarrier V)
    (h : ∀ i, (xs i).val = (ys i).val) : assignmentCode xs = assignmentCode ys := by
  unfold assignmentCode
  rw [funext h]

/-- No valid-code hypothesis is needed: a true code already supplies its syntax witness. -/
theorem satisfactionSet_trace {U V : ZFSet.{u}} (h : V ⊆ U) (hV : V.IsTransitive)
    {k : Nat} {I : Type v} [Small.{u} I] (code : I → ZFSet.{u})
    (M : Interpretation k I (ZFCarrier U)) (N : Interpretation k I (ZFCarrier V))
    (he : ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n) (xs : Fin n → ZFCarrier V),
      realize N φ Empty.elim xs ↔
        realize M φ Empty.elim (fun i => Auxiliary.inclusion h (xs i)))
    (e a : ZFSet.{u}) (ha : a ∈ V) :
    ZFSet.pair e a ∈ satisfactionSet code N ↔ ZFSet.pair e a ∈ satisfactionSet code M := by
  constructor
  · intro ht
    obtain ⟨⟨⟨n, φ⟩, ⟨xs, hx⟩⟩, heq⟩ := ZFSet.mem_range.mp ht
    refine ZFSet.mem_range.mpr ⟨⟨⟨n, φ⟩,
      ⟨(fun i => Auxiliary.inclusion h (xs i)), (he n φ xs).mp hx⟩⟩, ?_⟩
    exact heq
  · intro ht
    obtain ⟨⟨⟨n, φ⟩, ⟨xs, hx⟩⟩, heq⟩ := ZFSet.mem_range.mp ht
    have hxa : assignmentCode xs = a := (ZFSet.pair_inj.mp heq).2
    have hin := assignmentCode_entries_mem hV xs (hxa ▸ ha)
    let ys : Fin n → ZFCarrier V := fun i => ⟨(xs i).val, hin i⟩
    have hys : (fun i => Auxiliary.inclusion h (ys i)) = xs := by
      funext i
      exact Subtype.ext rfl
    have hy : realize N φ Empty.elim ys := (he n φ ys).mpr (by simpa only [hys] using hx)
    refine ZFSet.mem_range.mpr ⟨⟨⟨n, φ⟩, ⟨ys, hy⟩⟩, ?_⟩
    have hcode : assignmentCode ys = assignmentCode xs :=
      assignmentCode_eq_of_values_eq ys xs (fun _ => rfl)
    change ZFSet.pair _ (assignmentCode ys) = ZFSet.pair e a
    rw [hcode]
    exact heq

end OneYTruth
