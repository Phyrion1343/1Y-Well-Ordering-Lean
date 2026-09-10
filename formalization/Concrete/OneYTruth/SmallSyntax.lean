import OneYTruth.FormulaCode

/-!
# Set-sized syntax

Smallness is proved from a small type of index symbols. It is not installed
as an additional existence axiom. For ordinal initial segments, smallness
comes from their injection into the corresponding genuine ordinal ZF set.
-/

namespace OneYTruth.FormulaCode

open FirstOrder FirstOrder.Language

universe u v w

theorem Raw.map_leftInverse {I : Type v} {J : Type w} {f : I → J} {g : J → I}
    (h : Function.LeftInverse g f) : Function.LeftInverse (Raw.map g) (Raw.map f) := by
  intro φ
  induction φ <;> simp_all [Raw.map, Function.LeftInverse]

noncomputable instance rawSmall {I : Type v} [Small.{u} I] : Small.{u} (Raw I) := by
  let e : I ≃ Shrink.{u} I := equivShrink I
  exact small_of_injective (f := Raw.map e) (Raw.map_leftInverse e.left_inv).injective

noncomputable instance formulaSmall {I : Type v} [Small.{u} I] (k n : Nat) :
    Small.{u} ((OneYTruth.language k I).BoundedFormula Empty n) :=
  small_of_injective (toRaw_injective (k := k) (n := n))

noncomputable instance packedSmall {I : Type v} [Small.{u} I] (k : Nat) :
    Small.{u} (Packed k I) := inferInstanceAs (Small.{u} (Σ n,
      (OneYTruth.language k I).BoundedFormula Empty n))

noncomputable instance ordinalInitialSegmentSmall (η : Ordinal.{u}) :
    Small.{u} {ξ : Ordinal.{u} // ξ < η} := by
  let f : {ξ : Ordinal.{u} // ξ < η} → η.toZFSet :=
    fun i => ⟨i.val.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr i.property⟩
  apply small_of_injective (f := f)
  intro i j h
  apply Subtype.ext
  exact Ordinal.toZFSet_injective (congrArg Subtype.val h)

noncomputable instance ordinalClosedSegmentSmall (η : Ordinal.{u}) :
    Small.{u} {ξ : Ordinal.{u} // ξ ≤ η} := by
  let f : {ξ : Ordinal.{u} // ξ ≤ η} → {ξ : Ordinal.{u} // ξ < Order.succ η} :=
    fun i => ⟨i.val, Order.lt_succ_iff.mpr i.property⟩
  apply small_of_injective (f := f)
  intro i j h
  apply Subtype.ext
  exact congrArg (fun z : {ξ : Ordinal.{u} // ξ < Order.succ η} => z.val) h

end OneYTruth.FormulaCode
