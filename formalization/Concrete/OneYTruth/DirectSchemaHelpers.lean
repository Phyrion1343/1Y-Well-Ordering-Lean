import OneYTruth.AssignmentLookup

/-! Bounded assignment-extension queries for direct schema checking. -/

namespace OneYTruth.DirectSchema

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language FormulaCode InternalNodes CodedPaths BoundedEvaluation

universe u v

def Extends (p x q : ZFSet.{u}) : Prop :=
  Follows [true, false] q x ∧ ∃ t, Follows [true, true] q t ∧ Follows [true] p t

def extendsAt {n : Nat} (p x q : Fin n) : Delta0Formula n :=
  .conj (pathEqAt [true, false] q x) (pathsEqualAt [true, true] [true] q p)

theorem satisfies_extendsAt {n : Nat} (p x q : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (extendsAt p x q) s ↔ Extends (s p) (s x) (s q) := by
  simp only [extendsAt, Satisfies, satisfies_pathEqAt, satisfies_pathsEqualAt, Extends]

theorem extends_snoc {U : ZFSet.{u}} {n : Nat} (xs : Fin n → ZFCarrier U) (x : ZFCarrier U) :
    Extends (assignmentCode xs) x.val (assignmentCode (Fin.snoc xs x)) := by
  constructor
  · simp [assignmentCode_snoc, Follows]
  · refine ⟨assignmentPayload xs, ?_, ?_⟩
    · simp [assignmentCode_snoc, assignmentPayload, Follows]
    · simp [assignmentCode_eq_pair, Follows]

theorem extends_assignment_iff {U : ZFSet.{u}} {n : Nat}
    (xs : Fin n → ZFCarrier U) (x : ZFCarrier U) {q : ZFSet.{u}}
    (hq : q ∈ assignmentCodes U) :
    Extends (assignmentCode xs) x.val q ↔ q = assignmentCode (Fin.snoc xs x) := by
  constructor
  · intro h
    obtain ⟨⟨m, ys⟩, rfl⟩ := ZFSet.mem_range.mp hq
    exact assignmentCode_eq_snoc_of_payload xs ys x
      (AssignmentLookup.payload_eq_of_paths xs ys x h.1 h.2)
  · rintro rfl
    exact extends_snoc xs x

def ExtendedHolds (A S e p x : ZFSet.{u}) : Prop :=
  ∃ q ∈ A, Extends p x q ∧ ZFSet.pair e q ∈ S

def extendedHoldsAt {n : Nat} (A S e p x : Fin n) : Delta0Formula n :=
  .boundedEx A (.conj (extendsAt p.castSucc x.castSucc (Fin.last n))
    (pairMemAt S.castSucc e.castSucc (Fin.last n)))

theorem satisfies_extendedHoldsAt {n : Nat} (A S e p x : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (extendedHoldsAt A S e p x) s ↔
      ExtendedHolds (s A) (s S) (s e) (s p) (s x) := by
  simp only [extendedHoldsAt, Satisfies, satisfies_extendsAt, satisfies_pairMemAt,
    snoc_last, snoc_castSucc, ExtendedHolds]

theorem extendedHolds_codes {U : ZFSet.{u}} {n : Nat}
    (xs : Fin n → ZFCarrier U) (x : ZFCarrier U) (S e : ZFSet.{u}) :
    ExtendedHolds (assignmentCodes U) S e (assignmentCode xs) x.val ↔
      ZFSet.pair e (assignmentCode (Fin.snoc xs x)) ∈ S := by
  constructor
  · rintro ⟨q, hq, hExt, h⟩
    exact (extends_assignment_iff xs x hq).mp hExt ▸ h
  · intro h
    exact ⟨assignmentCode (Fin.snoc xs x),
      ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2)
        ⟨n + 1, Fin.snoc xs x⟩, extends_snoc xs x, h⟩

def DoubleHolds (A S e p x y : ZFSet.{u}) : Prop :=
  ∃ q ∈ A, Extends p x q ∧ ExtendedHolds A S e q y

def doubleHoldsAt {n : Nat} (A S e p x y : Fin n) : Delta0Formula n :=
  .boundedEx A (.conj (extendsAt p.castSucc x.castSucc (Fin.last n))
    (extendedHoldsAt A.castSucc S.castSucc e.castSucc (Fin.last n) y.castSucc))

theorem satisfies_doubleHoldsAt {n : Nat} (A S e p x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (doubleHoldsAt A S e p x y) s ↔
      DoubleHolds (s A) (s S) (s e) (s p) (s x) (s y) := by
  simp only [doubleHoldsAt, Satisfies, satisfies_extendsAt, satisfies_extendedHoldsAt,
    snoc_last, snoc_castSucc, DoubleHolds]

theorem doubleHolds_codes {U : ZFSet.{u}} {n : Nat}
    (xs : Fin n → ZFCarrier U) (x y : ZFCarrier U) (S e : ZFSet.{u}) :
    DoubleHolds (assignmentCodes U) S e (assignmentCode xs) x.val y.val ↔
      ZFSet.pair e (assignmentCode (Fin.snoc (Fin.snoc xs x) y)) ∈ S := by
  constructor
  · rintro ⟨q, hq, hExt, h⟩
    have he := (extends_assignment_iff xs x hq).mp hExt
    rw [he, extendedHolds_codes] at h
    exact h
  · intro h
    refine ⟨assignmentCode (Fin.snoc xs x),
      ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2)
        ⟨n + 1, Fin.snoc xs x⟩, extends_snoc xs x, ?_⟩
    exact (extendedHolds_codes _ _ _ _).mpr h

theorem mem_scopedPairs_iff_arity {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) {n m : Nat}
    (φ : (language k I).BoundedFormula Empty n) (xs : Fin m → ZFCarrier U) :
    ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode xs) ∈
      scopedPairs (k := k) U indexCode ↔ n = m := by
  constructor
  · intro h
    obtain ⟨⟨⟨l, ψ⟩, ys⟩, he⟩ := ZFSet.mem_range.mp h
    obtain ⟨hφ, hxs⟩ := ZFSet.pair_inj.mp he
    have hln : l = n := natCode_injective (ZFSet.pair_inj.mp hφ).1
    have hlm : l = m := assignmentCode_arity_eq hxs
    omega
  · intro h
    subst m
    exact ZFSet.mem_range_self (f := fun w : ScopedAssignment (k := k) I U =>
      ZFSet.pair (packedCode indexCode w.1) (assignmentCode w.2)) ⟨⟨n, φ⟩, xs⟩

def ScopeOne (U A nodes e p : ZFSet.{u}) : Prop :=
  ∃ x ∈ U, ExtendedHolds A nodes e p x

def scopeOneAt {n : Nat} (U A nodes e p : Fin n) : Delta0Formula n :=
  .boundedEx U (extendedHoldsAt A.castSucc nodes.castSucc e.castSucc p.castSucc (Fin.last n))

theorem satisfies_scopeOneAt {n : Nat} (U A nodes e p : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (scopeOneAt U A nodes e p) s ↔
      ScopeOne (s U) (s A) (s nodes) (s e) (s p) := by
  simp only [scopeOneAt, Satisfies, satisfies_extendedHoldsAt, snoc_last, snoc_castSucc, ScopeOne]

theorem scopeOne_codes {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} [Nonempty (ZFCarrier U)] (indexCode : I → ZFSet.{u}) {n m : Nat}
    (φ : (language k I).BoundedFormula Empty n) (xs : Fin m → ZFCarrier U) :
    ScopeOne U (assignmentCodes U) (scopedPairs (k := k) U indexCode)
      (packedCode indexCode ⟨n, φ⟩) (assignmentCode xs) ↔ n = m + 1 := by
  constructor
  · rintro ⟨x, hx, h⟩
    have hh := (extendedHolds_codes xs (⟨x, hx⟩ : ZFCarrier U) _ _).mp h
    exact (mem_scopedPairs_iff_arity indexCode φ _).mp hh
  · intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty (ZFCarrier U))
    exact ⟨x.val, x.property, (extendedHolds_codes xs x _ _).mpr
      ((mem_scopedPairs_iff_arity indexCode φ _).mpr h)⟩

def ScopeTwo (U A nodes e p : ZFSet.{u}) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, DoubleHolds A nodes e p x y

def scopeTwoAt {n : Nat} (U A nodes e p : Fin n) : Delta0Formula n :=
  .boundedEx U (.boundedEx U.castSucc
    (doubleHoldsAt A.castSucc.castSucc nodes.castSucc.castSucc e.castSucc.castSucc
      p.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1))))

theorem satisfies_scopeTwoAt {n : Nat} (U A nodes e p : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (scopeTwoAt U A nodes e p) s ↔
      ScopeTwo (s U) (s A) (s nodes) (s e) (s p) := by
  simp only [scopeTwoAt, Satisfies, satisfies_doubleHoldsAt, snoc_last, snoc_castSucc, ScopeTwo]

theorem scopeTwo_codes {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} [Nonempty (ZFCarrier U)] (indexCode : I → ZFSet.{u}) {n m : Nat}
    (φ : (language k I).BoundedFormula Empty n) (xs : Fin m → ZFCarrier U) :
    ScopeTwo U (assignmentCodes U) (scopedPairs (k := k) U indexCode)
      (packedCode indexCode ⟨n, φ⟩) (assignmentCode xs) ↔ n = m + 2 := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    have hh := (doubleHolds_codes xs (⟨x, hx⟩ : ZFCarrier U) ⟨y, hy⟩ _ _).mp h
    exact (mem_scopedPairs_iff_arity indexCode φ _).mp hh
  · intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty (ZFCarrier U))
    exact ⟨x.val, x.property, x.val, x.property, (doubleHolds_codes xs x x _ _).mpr
      ((mem_scopedPairs_iff_arity indexCode φ _).mpr h)⟩

end OneYTruth.DirectSchema
