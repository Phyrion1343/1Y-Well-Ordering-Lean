import OneYTruth.AssignmentLookup

/-! A literal bounded step for variable lookup, using head/tail inheritance. -/

namespace OneYTruth.AssignmentLookup

open Constructible Constructible.Delta0Formula Constructible.Godel CodedPaths BoundedEvaluation

universe u

/-- Bound, assignments, omega, domain, state, candidate; then six witnesses. -/
def lookupBody : Delta0Formula 12 :=
  .conj (tripleEqAt 5 6 7 8)
    (.conj (pathEqAt [false] 9 10)
      (.conj (pathEqAt [true, false] 6 11)
        (.conj (pathsEqualAt [true, true] [true] 6 9)
          (.disj (.conj (.eq 7 10) (.eq 8 11)) (tripleMemAt 4 9 7 8)))))

theorem satisfies_lookupBody (s : Tuple ZFSet.{u} 12) :
    Satisfies ZFMem lookupBody s ↔ s 5 = triple (s 6) (s 7) (s 8) ∧
      Follows [false] (s 9) (s 10) ∧ Follows [true, false] (s 6) (s 11) ∧
      (∃ t, Follows [true, true] (s 6) t ∧ Follows [true] (s 9) t) ∧
      ((s 7 = s 10 ∧ s 8 = s 11) ∨ triple (s 9) (s 7) (s 8) ∈ s 4) := by
  simp only [lookupBody, Satisfies, satisfies_tripleEqAt, satisfies_pathEqAt,
    satisfies_pathsEqualAt, satisfies_disj, satisfies_tripleMemAt]

attribute [irreducible] lookupBody

def lookupFormula : Delta0Formula 6 :=
  .boundedEx 1 (.boundedEx 2 (.boundedEx 3
    (.boundedEx 1 (.boundedEx 2 (.boundedEx 3 lookupBody)))))

def LookupRule (A W U S z : ZFSet.{u}) : Prop :=
  ∃ parent ∈ A, ∃ i ∈ W, ∃ x ∈ U, ∃ child ∈ A, ∃ N ∈ W, ∃ a ∈ U,
    z = triple parent i x ∧ Follows [false] child N ∧ Follows [true, false] parent a ∧
    (∃ t, Follows [true, true] parent t ∧ Follows [true] child t) ∧
    ((i = N ∧ x = a) ∨ triple child i x ∈ S)

theorem satisfies_lookupFormula (B A W U S z : ZFSet.{u}) :
    Satisfies ZFMem lookupFormula ![B, A, W, U, S, z] ↔ LookupRule A W U S z := by
  simp only [lookupFormula, Satisfies, satisfies_lookupBody]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, LookupRule, ZFMem]

open Constructible.FiniteSequenceZF InternalNodes
open Constructible.IndexedSequenceZF (mem_omega_iff_exists_natCode)

theorem lookupRule_snoc {U : ZFSet.{u}} {n : Nat} (v : Fin n → ZFCarrier U)
    (a : ZFCarrier U) (i : Fin (n + 1)) (S : ZFSet.{u})
    (hcase : ((natCode i.val : ZFSet.{u}) = natCode n ∧
      ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).val = a.val) ∨
      triple (assignmentCode v) (natCode i.val) ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).val ∈ S) :
    LookupRule (assignmentCodes U) Ordinal.omega0.toZFSet U S
      (triple (assignmentCode (Fin.snoc v a)) (natCode i.val)
        ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).val) := by
  refine ⟨assignmentCode (Fin.snoc v a),
    ZFSet.mem_range_self (f := fun z : PackedAssignment U => assignmentCode z.2) ⟨n + 1, Fin.snoc v a⟩,
    natCode i.val, (mem_omega_iff_exists_natCode _).mpr ⟨i.val, rfl⟩,
    ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).val,
    ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).property,
    assignmentCode v,
    ZFSet.mem_range_self (f := fun z : PackedAssignment U => assignmentCode z.2) ⟨n, v⟩,
    natCode n, (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩,
    a.val, a.property, rfl, ?_, ?_, ?_, hcase⟩
  · rw [assignmentCode_eq_pair, follows_pair]
    rfl
  · rw [assignmentCode_snoc, follows_pair, if_pos rfl, follows_pair]
    rfl
  · refine ⟨assignmentPayload v, ?_, ?_⟩
    · rw [assignmentCode_snoc, follows_pair, if_pos rfl, follows_pair]
      rfl
    · rw [assignmentCode_eq_pair, follows_pair]
      rfl

end OneYTruth.AssignmentLookup
