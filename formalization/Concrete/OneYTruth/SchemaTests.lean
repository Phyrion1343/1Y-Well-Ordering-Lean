import OneYTruth.SchemaQueries
import OneYTruth.SatisfactionSet
import OneYTruth.DeltaZeroBridge
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel

/-!
# The actual sets of schema-test nodes

All formulas and all finite assignments are included in genuine set ranges.
Checking their inclusion in the actual satisfaction set is exactly checking
the expanded schema. Constructibility and internal supply of the complete
test sets remain separate obligations; individual code closure is not used
as a substitute for them.
-/

namespace OneYTruth.SchemaTests

open FirstOrder FirstOrder.Language Constructible FormulaCode SchemaQueries

universe u v

abbrev QueryInput (k : Nat) (I : Type v) (U : ZFSet.{u}) (shift : Nat) :=
  Σ n : Nat, (language k I).BoundedFormula Empty (n + shift) ×
    (Fin n → ZFCarrier U) × ZFCarrier U

noncomputable def queryTests {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) {shift : Nat}
    (query : ∀ n, (language k I).BoundedFormula Empty (n + shift) →
      (language k I).BoundedFormula Empty (n + 1)) : ZFSet.{u} :=
  ZFSet.range (fun w : QueryInput k I U shift =>
    ZFSet.pair (packedCode indexCode ⟨w.1 + 1, query w.1 w.2.1⟩)
      (assignmentCode (Fin.snoc w.2.2.1 w.2.2.2)))

theorem queryTests_subset_iff {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) {shift : Nat}
    (query : ∀ n, (language k I).BoundedFormula Empty (n + shift) →
      (language k I).BoundedFormula Empty (n + 1)) :
    queryTests indexCode U query ⊆ satisfactionSet indexCode M ↔
      ∀ n (φ : (language k I).BoundedFormula Empty (n + shift))
        (xs : Fin n → ZFCarrier U) (a : ZFCarrier U),
          realize M (query n φ) Empty.elim (Fin.snoc xs a) := by
  constructor
  · intro h n φ xs a
    apply (mem_satisfactionSet_iff hi M _ _).mp
    exact h (ZFSet.mem_range_self (f := fun w : QueryInput k I U shift =>
      ZFSet.pair (packedCode indexCode ⟨w.1 + 1, query w.1 w.2.1⟩)
        (assignmentCode (Fin.snoc w.2.2.1 w.2.2.2))) ⟨n, φ, xs, a⟩)
  · intro h p hp
    obtain ⟨⟨n, φ, xs, a⟩, rfl⟩ := ZFSet.mem_range.mp hp
    exact (mem_satisfactionSet_iff hi M _ _).mpr (h n φ xs a)

noncomputable def separationTests {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) : ZFSet.{u} :=
  queryTests (k := k) indexCode U (fun _ => separationQuery)

noncomputable def collectionTests {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) : ZFSet.{u} :=
  queryTests (k := k) indexCode U (fun _ => collectionSchema)

theorem separationTests_subset_iff {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (hmem : M.mem = zfCarrierMem U) :
    separationTests (k := k) indexCode U ⊆ satisfactionSet indexCode M ↔ InternalClosure.HasSeparation M :=
  (queryTests_subset_iff indexCode hi M _).trans (hasSeparation_iff_queries M hmem).symm

theorem collectionTests_subset_iff {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (hmem : M.mem = zfCarrierMem U) :
    collectionTests (k := k) indexCode U ⊆ satisfactionSet indexCode M ↔ InternalClosure.HasCollection M :=
  (queryTests_subset_iff indexCode hi M _).trans (hasCollection_iff_queries M hmem).symm

/-- Three coordinates: Separation tests, Collection tests, actual satisfaction. -/
def checkFormula : Delta0Formula 3 :=
  .conj (Delta0Formula.subsetAt 0 2) (Delta0Formula.subsetAt 1 2)

def mixedCheckFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I checkFormula

theorem mixedCheckFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedCheckFormula k I) := ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_check_iff_schemas {k : Nat} {I : Type v} [Small.{u} I]
    {U W : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (hmem : M.mem = zfCarrierMem U)
    {K : Nat} {J : Type v} (hW : W.IsTransitive) (N : Interpretation K J (ZFCarrier W))
    (hNmem : N.mem = zfCarrierMem W) (p : Fin 3 → ZFCarrier W)
    (hp0 : (p 0).val = separationTests (k := k) indexCode U)
    (hp1 : (p 1).val = collectionTests (k := k) indexCode U)
    (hp2 : (p 2).val = satisfactionSet indexCode M) :
    realize N (mixedCheckFormula K J) Empty.elim p ↔
      InternalClosure.HasSeparation M ∧ InternalClosure.HasCollection M := by
  rw [mixedCheckFormula, realize_ofConstructibleDeltaZero_absolute hW N hNmem]
  simp only [checkFormula, Delta0Formula.Satisfies, Delta0Formula.satisfies_subsetAt]
  change ((p 0).val ⊆ (p 2).val ∧ (p 1).val ⊆ (p 2).val) ↔ _
  rw [hp0, hp1, hp2, separationTests_subset_iff indexCode hi M hmem,
    collectionTests_subset_iff indexCode hi M hmem]

end OneYTruth.SchemaTests

#print axioms OneYTruth.SchemaTests.queryTests_subset_iff
#print axioms OneYTruth.SchemaTests.realize_check_iff_schemas
