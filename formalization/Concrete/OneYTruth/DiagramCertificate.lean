import OneYTruth.SyntaxDiagram

/-!
# The explicit bounded diagram test characterizes full satisfaction

The diagram is constructed from real syntax and atomic interpretations.
Its bounded solution formula is equivalent to the Tarski recursion and
therefore characterizes the actual satisfaction set uniquely. To use this
inside a chosen model one must still supply membership of the seven real
set parameters in that model; this file does not assume their existence
inside a constructible level.
-/

namespace OneYTruth.SyntaxDiagram

open FirstOrder FirstOrder.Language Constructible FormulaCode BoundedEvaluation

universe u v w

theorem isSolution_iff_tarskiSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u}) :
    IsSolution (diagram indexCode M) S ↔ IsTarskiSet indexCode M S := by
  constructor
  · intro h
    have ha {n : Nat} (φ : (language k I).BoundedFormula Empty n)
        (v : Fin n → ZFCarrier U) (hA : IsAtomic φ) :
        CodedHolds indexCode S φ v ↔ OneYTruth.realize M φ Empty.elim v := by
      have hm : nodeCode indexCode ⟨⟨n, φ⟩, v⟩ ∈ (diagram indexCode M).atoms :=
        ZFSet.mem_range_self (f := fun z : AtomicAssignment (k := k) I U =>
          nodeCode indexCode z.val) ⟨⟨⟨n, φ⟩, v⟩, hA⟩
      exact (h.2.1 _ hm).trans ((mem_trueAtomSet_iff hi M ⟨⟨n, φ⟩, v⟩).trans
        (and_iff_right hA))
    refine ⟨h.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro n v
      rw [ha (.falsum : (language k I).BoundedFormula Empty n) v trivial]
      exact not_false
    · intro n t s v
      exact ha (.equal t s) v trivial
    · intro n m r ts v
      exact ha (.rel r ts) v trivial
    · intro n φ ψ v
      apply h.2.2.1 _ (nodeCode_mem_scopedPairs indexCode ⟨⟨n, .imp φ ψ⟩, v⟩)
        _ (nodeCode_mem_scopedPairs indexCode ⟨⟨n, φ⟩, v⟩)
        _ (nodeCode_mem_scopedPairs indexCode ⟨⟨n, ψ⟩, v⟩)
      exact ZFSet.mem_range_self (f := fun z : ImplicationAssignment (k := k) I U =>
        Godel.triple (nodeCode indexCode ⟨⟨z.1, .imp z.2.1.1 z.2.1.2⟩, z.2.2⟩)
          (nodeCode indexCode ⟨⟨z.1, z.2.1.1⟩, z.2.2⟩)
          (nodeCode indexCode ⟨⟨z.1, z.2.1.2⟩, z.2.2⟩)) ⟨n, (φ, ψ), v⟩
    · intro n φ v
      let w : QuantifiedAssignment (k := k) I U := ⟨n, φ, v⟩
      have hp : nodeCode indexCode (quantifiedParent w) ∈ (diagram indexCode M).quantified :=
        ZFSet.mem_range_self w
      exact (h.2.2.2 _ hp).trans (all_children_iff hi S w)
  · intro h
    refine ⟨h.noJunk, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨⟨z, hzA⟩, heq⟩ := ZFSet.mem_range.mp hp
      subst p
      exact (h.correct z.1.2 z.2).trans
        ((mem_trueAtomSet_iff hi M z).trans (and_iff_right hzA)).symm
    · intro p _ a _ b _ ht
      obtain ⟨⟨n, ⟨φ, ψ⟩, v⟩, heq⟩ := ZFSet.mem_range.mp ht
      obtain ⟨hp, hab⟩ := ZFSet.pair_inj.mp heq
      obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hab
      subst p
      subst a
      subst b
      exact h.imp φ ψ v
    · intro p hp
      obtain ⟨z, heq⟩ := ZFSet.mem_range.mp hp
      subst p
      exact (h.all z.2.1 z.2.2).trans (all_children_iff hi S z).symm

/-- The explicitly coded diagram has exactly the canonical full satisfaction solution. -/
theorem isSolution_iff_eq_satisfactionSet {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u}) :
    IsSolution (diagram indexCode M) S ↔ S = satisfactionSet indexCode M := by
  rw [isSolution_iff_tarskiSet hi M S]
  exact ⟨fun h => h.eq_satisfactionSet hi, fun h => h ▸ satisfactionSet_isTarskiSet hi M⟩

/-- Given its actual parameters in a transitive ambient model, the bounded formula
recognizes the complete satisfaction set of the fixed smaller set domain. -/
theorem realize_certificate_iff_eq_satisfactionSet
    {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U V : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u})
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (p : Fin 7 → ZFCarrier V)
    (hp : ∀ i, (p i).val = parameters (diagram indexCode M) S i) :
    OneYTruth.realize N (mixedSolutionFormula K J) Empty.elim p ↔
      S = satisfactionSet indexCode M :=
  (realize_mixedSolutionFormula hV N hmem _ S p hp).trans
    (isSolution_iff_eq_satisfactionSet hi M S)

end OneYTruth.SyntaxDiagram
