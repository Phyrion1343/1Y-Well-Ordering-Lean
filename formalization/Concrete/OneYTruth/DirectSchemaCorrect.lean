import OneYTruth.DirectSchemaFormula

/-! Exact correctness of the direct bounded schema check on canonical sources. -/

namespace OneYTruth.DirectSchema

open Constructible FirstOrder FirstOrder.Language FormulaCode InternalNodes

universe u v w

theorem extendedHolds_satisfaction {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 1))
    (xs : Fin n → ZFCarrier U) (x : ZFCarrier U) :
    ExtendedHolds (assignmentCodes U) (satisfactionSet indexCode M)
      (packedCode indexCode ⟨n + 1, φ⟩) (assignmentCode xs) x.val ↔
        realize M φ Empty.elim (Fin.snoc xs x) :=
  (extendedHolds_codes xs x _ _).trans (mem_satisfactionSet_iff hi M φ _)

theorem doubleHolds_satisfaction {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2))
    (xs : Fin n → ZFCarrier U) (x y : ZFCarrier U) :
    DoubleHolds (assignmentCodes U) (satisfactionSet indexCode M)
      (packedCode indexCode ⟨n + 2, φ⟩) (assignmentCode xs) x.val y.val ↔
        realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y) :=
  (doubleHolds_codes xs x y _ _).trans (mem_satisfactionSet_iff hi M φ _)

theorem separation_iff_schema {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} [Nonempty (ZFCarrier U)]
    (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) :
    Separation U (syntaxCodes (k := k) indexCode) (assignmentCodes U)
      (scopedPairs (k := k) U indexCode) (satisfactionSet indexCode M) ↔
        InternalClosure.HasSeparation M := by
  constructor
  · intro h n φ xs a
    obtain ⟨b, hbU, hb⟩ := h (packedCode indexCode ⟨n + 1, φ⟩)
      (ZFSet.mem_range_self (f := packedCode (k := k) indexCode) ⟨n + 1, φ⟩)
      (assignmentCode xs)
      (ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2) ⟨n, xs⟩)
      ((scopeOne_codes indexCode φ xs).mpr rfl) a.val a.property
    refine ⟨⟨b, hbU⟩, fun x => ?_⟩
    exact (hb x.val x.property).trans (and_congr Iff.rfl
      (extendedHolds_satisfaction indexCode hi M φ xs x))
  · intro h e he p hp hs a ha
    obtain ⟨⟨m, φ⟩, rfl⟩ := ZFSet.mem_range.mp he
    obtain ⟨⟨n, xs⟩, rfl⟩ := ZFSet.mem_range.mp hp
    have hmn : m = n + 1 := (scopeOne_codes indexCode φ xs).mp hs
    subst m
    obtain ⟨b, hb⟩ := h n φ xs ⟨a, ha⟩
    refine ⟨b.val, b.property, fun x hx => ?_⟩
    exact (hb ⟨x, hx⟩).trans (and_congr Iff.rfl
      (extendedHolds_satisfaction indexCode hi M φ xs ⟨x, hx⟩).symm)

theorem collection_iff_schema {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} [Nonempty (ZFCarrier U)]
    (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) :
    Collection U (syntaxCodes (k := k) indexCode) (assignmentCodes U)
      (scopedPairs (k := k) U indexCode) (satisfactionSet indexCode M) ↔
        InternalClosure.HasCollection M := by
  constructor
  · intro h n φ xs a ht
    have ht' : ∀ x ∈ U, x ∈ a.val → ∃ y ∈ U,
        DoubleHolds (assignmentCodes U) (satisfactionSet indexCode M)
          (packedCode indexCode ⟨n + 2, φ⟩) (assignmentCode xs) x y := by
      intro x hx hxa
      obtain ⟨y, hy⟩ := ht ⟨x, hx⟩ hxa
      exact ⟨y.val, y.property, (doubleHolds_satisfaction indexCode hi M φ xs ⟨x, hx⟩ y).mpr hy⟩
    obtain ⟨b, hbU, hb⟩ := h (packedCode indexCode ⟨n + 2, φ⟩)
      (ZFSet.mem_range_self (f := packedCode (k := k) indexCode) ⟨n + 2, φ⟩)
      (assignmentCode xs)
      (ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2) ⟨n, xs⟩)
      ((scopeTwo_codes indexCode φ xs).mpr rfl) a.val a.property ht'
    refine ⟨⟨b, hbU⟩, fun x hxa => ?_⟩
    obtain ⟨y, hyU, hyb, hy⟩ := hb x.val x.property hxa
    exact ⟨⟨y, hyU⟩, hyb, (doubleHolds_satisfaction indexCode hi M φ xs x ⟨y, hyU⟩).mp hy⟩
  · intro h e he p hp hs a ha ht
    obtain ⟨⟨m, φ⟩, rfl⟩ := ZFSet.mem_range.mp he
    obtain ⟨⟨n, xs⟩, rfl⟩ := ZFSet.mem_range.mp hp
    have hmn : m = n + 2 := (scopeTwo_codes indexCode φ xs).mp hs
    subst m
    have ht' : ∀ x : ZFCarrier U, x.val ∈ a → ∃ y : ZFCarrier U,
        realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y) := by
      intro x hxa
      obtain ⟨y, hyU, hy⟩ := ht x.val x.property hxa
      exact ⟨⟨y, hyU⟩, (doubleHolds_satisfaction indexCode hi M φ xs x ⟨y, hyU⟩).mp hy⟩
    obtain ⟨b, hb⟩ := h n φ xs ⟨a, ha⟩ ht'
    refine ⟨b.val, b.property, fun x hx hxa => ?_⟩
    obtain ⟨y, hyb, hy⟩ := hb ⟨x, hx⟩ hxa
    exact ⟨y.val, y.property, hyb,
      (doubleHolds_satisfaction indexCode hi M φ xs ⟨x, hx⟩ y).mpr hy⟩

def mixedCheckFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I checkFormula

theorem mixedCheckFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedCheckFormula k I) := ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_check_iff_schemas {k : Nat} {I : Type v} [Small.{u} I]
    {U W : ZFSet.{u}} [Nonempty (ZFCarrier U)]
    (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    {K : Nat} {J : Type w} (hW : W.IsTransitive)
    (N : Interpretation K J (ZFCarrier W)) (hNmem : N.mem = zfCarrierMem W)
    (p : Fin 5 → ZFCarrier W)
    (hp : ∀ i, (p i).val = ![U, syntaxCodes (k := k) indexCode, assignmentCodes U,
      scopedPairs (k := k) U indexCode, satisfactionSet indexCode M] i) :
    realize N (mixedCheckFormula K J) Empty.elim p ↔
      InternalClosure.HasSeparation M ∧ InternalClosure.HasCollection M := by
  rw [mixedCheckFormula, realize_ofConstructibleDeltaZero_absolute hW N hNmem]
  have he : Delta0Formula.val p = ![U, syntaxCodes (k := k) indexCode, assignmentCodes U,
      scopedPairs (k := k) U indexCode, satisfactionSet indexCode M] := funext hp
  rw [he, satisfies_checkFormula, separation_iff_schema indexCode hi M,
    collection_iff_schema indexCode hi M]

end OneYTruth.DirectSchema

#print axioms OneYTruth.DirectSchema.mixedCheckFormula_isDeltaZero
#print axioms OneYTruth.DirectSchema.realize_check_iff_schemas
