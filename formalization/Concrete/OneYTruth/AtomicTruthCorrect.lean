import OneYTruth.AtomicTruthFormula

/-! Correctness of the bounded atomic truth test on the actual atomic source. -/

namespace OneYTruth.AtomicTruthFormula

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.Godel
open AtomicArgumentLookup AtomicRelationGraphs CodedPaths BoundedEvaluation
open FormulaCode SyntaxDiagram InternalNodes AssignmentLookup
open Constructible.IndexedSequenceZF (mem_omega_iff_exists_natCode)

universe u v

noncomputable def parameters {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) :
    Tuple ZFSet.{u} 11 :=
  ![U, lookupSet U, assignmentCodes U, Ordinal.omega0.toZFSet,
    ZFSet.range indexCode, namedGraph indexCode M, diagonalGraph M,
    natCode 1, natCode 2, natCode 3, natCode 4]

theorem satisfies_formula {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) (z : ZFSet.{u}) :
    Satisfies ZFMem formula (snoc (parameters indexCode M) z) ↔
    (Follows (argumentPath 0) z (natCode 1) ∧ ∃ x ∈ U,
      Argument (argumentPath 1) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z x ∧
      Argument (argumentPath 2) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z x) ∨
    (Follows (argumentPath 0) z (natCode 2) ∧ ∃ x ∈ U, ∃ y ∈ U,
      Argument (argumentPath 1) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z x ∧
      Argument (argumentPath 2) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z y ∧ x ∈ y) ∨
    (Follows (argumentPath 0) z (natCode 3) ∧ ∃ j ∈ Ordinal.omega0.toZFSet,
      ∃ ξ ∈ U, ∃ e ∈ U, ∃ a ∈ U,
      Follows (argumentPath 1) z j ∧
      Argument (argumentPath 2) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z ξ ∧
      Argument (argumentPath 3) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z e ∧
      Argument (argumentPath 4) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z a ∧
      quad j ξ e a ∈ diagonalGraph M) ∨
    (Follows (argumentPath 0) z (natCode 4) ∧ ∃ ξ ∈ ZFSet.range indexCode,
      ∃ e ∈ U, ∃ a ∈ U,
      Follows (argumentPath 1) z ξ ∧
      Argument (argumentPath 2) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z e ∧
      Argument (argumentPath 3) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet z a ∧
      triple ξ e a ∈ namedGraph indexCode M) := by
  simp only [formula, Satisfies, satisfies_disj, satisfies_pathEqAt,
    satisfies_equalityAt, satisfies_membershipAt, satisfies_diagonalAt, satisfies_namedAt]
  rfl

theorem follows_codedNode_tag {U : ZFSet.{u}} {n : Nat} (tag : ZFSet.{u})
    (rest : List ZFSet.{u}) (v : Fin n → ZFCarrier U) (x : ZFSet.{u}) :
    Follows (argumentPath 0) (codedNode (tag :: rest) v) x ↔ x = tag :=
  follows_codedNode_field (tag :: rest) v ⟨0, by simp⟩ x

theorem term_realize_index {k : Nat} {I : Type v} {U : ZFSet.{u}} {n : Nat}
    (M : Interpretation k I (ZFCarrier U)) (v : Fin n → ZFCarrier U)
    (t : (language k I).Term (Empty ⊕ Fin n)) :
    @Term.realize (language k I) (ZFCarrier U) M.structure (Empty ⊕ Fin n)
      (Sum.elim Empty.elim v) t = v (termIndex t) := by
  rw [← var_termIndex t]
  rfl

theorem satisfies_formula_atomic {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hmem : ∀ x y, M.mem x y ↔ x.val ∈ y.val)
    {n : Nat} (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U)
    (hφ : IsAtomic φ) :
    Satisfies ZFMem formula (snoc (parameters indexCode M) (nodeCode indexCode ⟨⟨n, φ⟩, v⟩)) ↔
      OneYTruth.realize M φ Empty.elim v := by
  rw [satisfies_formula]
  cases φ with
  | falsum =>
    change _ ↔ False
    have hn : nodeCode (k := k) indexCode ⟨⟨n, .falsum⟩, v⟩ = codedNode [natCode 0] v := rfl
    simp only [hn]
    simp only [follows_codedNode_tag, natCode_inj, Nat.reduceEqDiff, false_and, false_or]
  | equal t s =>
    let fields : List ZFSet.{u} := [natCode 1, natCode (termIndex t).val, natCode (termIndex s).val]
    have h1 := fun x => argument_codedNode_iff fields v ⟨1, by simp [fields]⟩ (termIndex t) rfl x
    have h2 := fun x => argument_codedNode_iff fields v ⟨2, by simp [fields]⟩ (termIndex s) rfl x
    change _ ↔ @Term.realize _ _ M.structure _ _ t = @Term.realize _ _ M.structure _ _ s
    rw [term_realize_index, term_realize_index]
    simp only [show nodeCode indexCode ⟨⟨n, .equal t s⟩, v⟩ = codedNode fields v from rfl]
    simp only [fields, follows_codedNode_tag, natCode_inj, Nat.reduceEqDiff, true_and,
      false_and, false_or, or_false]
    change (∃ x ∈ U, Argument _ _ _ _ (codedNode fields v) x ∧ Argument _ _ _ _ (codedNode fields v) x) ↔ _
    simp only [h1, h2]
    constructor
    · rintro ⟨x, _, hx, hy⟩
      exact Subtype.ext (hx.trans hy.symm)
    · intro h
      exact ⟨(v (termIndex t)).val, (v (termIndex t)).property, rfl,
        congrArg (fun x : ZFCarrier U => x.val) h.symm⟩
  | rel r ts =>
    cases r with
    | mem =>
      let fields : List ZFSet.{u} := [natCode 2, natCode (termIndex (ts 0)).val, natCode (termIndex (ts 1)).val]
      have h1 := fun x => argument_codedNode_iff fields v ⟨1, by simp [fields]⟩ (termIndex (ts 0)) rfl x
      have h2 := fun x => argument_codedNode_iff fields v ⟨2, by simp [fields]⟩ (termIndex (ts 1)) rfl x
      change _ ↔ M.mem (@Term.realize _ _ M.structure _ _ (ts 0)) (@Term.realize _ _ M.structure _ _ (ts 1))
      rw [term_realize_index, term_realize_index, hmem]
      simp only [show nodeCode indexCode ⟨⟨n, .rel .mem ts⟩, v⟩ = codedNode fields v from rfl]
      simp only [fields, follows_codedNode_tag, natCode_inj, Nat.reduceEqDiff, true_and,
        false_and, false_or, or_false]
      change (∃ x ∈ U, ∃ y ∈ U, Argument _ _ _ _ (codedNode fields v) x ∧
        Argument _ _ _ _ (codedNode fields v) y ∧ x ∈ y) ↔ _
      simp only [h1, h2]
      constructor
      · rintro ⟨x, _, y, _, hx, hy, hxy⟩
        simpa only [hx, hy] using hxy
      · intro h
        exact ⟨_, (v (termIndex (ts 0))).property, _, (v (termIndex (ts 1))).property, rfl, rfl, h⟩
    | diagonal j =>
      let fields : List ZFSet.{u} := [natCode 3, natCode j.val, natCode (termIndex (ts 0)).val,
        natCode (termIndex (ts 1)).val, natCode (termIndex (ts 2)).val]
      have hj := fun x => follows_codedNode_field fields v ⟨1, by simp [fields]⟩ x
      have h2 := fun x => argument_codedNode_iff fields v ⟨2, by simp [fields]⟩ (termIndex (ts 0)) rfl x
      have h3 := fun x => argument_codedNode_iff fields v ⟨3, by simp [fields]⟩ (termIndex (ts 1)) rfl x
      have h4 := fun x => argument_codedNode_iff fields v ⟨4, by simp [fields]⟩ (termIndex (ts 2)) rfl x
      change _ ↔ M.diagonal j (@Term.realize _ _ M.structure _ _ (ts 0))
        (@Term.realize _ _ M.structure _ _ (ts 1)) (@Term.realize _ _ M.structure _ _ (ts 2))
      rw [term_realize_index, term_realize_index, term_realize_index]
      rw [← mem_diagonalGraph_iff]
      simp only [show nodeCode indexCode ⟨⟨n, .rel (.diagonal j) ts⟩, v⟩ = codedNode fields v from rfl]
      simp only [fields, follows_codedNode_tag, natCode_inj, Nat.reduceEqDiff, true_and,
        false_and, false_or, or_false]
      change (∃ z ∈ Ordinal.omega0.toZFSet, ∃ x ∈ U, ∃ y ∈ U, ∃ a ∈ U,
        Follows _ (codedNode fields v) z ∧ Argument _ _ _ _ (codedNode fields v) x ∧
        Argument _ _ _ _ (codedNode fields v) y ∧ Argument _ _ _ _ (codedNode fields v) a ∧ _) ↔ _
      simp only [hj, h2, h3, h4]
      constructor
      · rintro ⟨z, _, x, _, y, _, a, _, hz, hx, hy, ha, h⟩
        change z = natCode j.val at hz
        simpa only [← hx, ← hy, ← ha, hz] using h
      · intro h
        exact ⟨_, (mem_omega_iff_exists_natCode _).mpr ⟨j.val, rfl⟩,
          _, (v (termIndex (ts 0))).property, _, (v (termIndex (ts 1))).property,
          _, (v (termIndex (ts 2))).property, rfl, rfl, rfl, rfl, h⟩
    | named i =>
      let fields : List ZFSet.{u} := [natCode 4, indexCode i, natCode (termIndex (ts 0)).val,
        natCode (termIndex (ts 1)).val]
      have hi' := fun x => follows_codedNode_field fields v ⟨1, by simp [fields]⟩ x
      have h2 := fun x => argument_codedNode_iff fields v ⟨2, by simp [fields]⟩ (termIndex (ts 0)) rfl x
      have h3 := fun x => argument_codedNode_iff fields v ⟨3, by simp [fields]⟩ (termIndex (ts 1)) rfl x
      change _ ↔ M.named i (@Term.realize _ _ M.structure _ _ (ts 0)) (@Term.realize _ _ M.structure _ _ (ts 1))
      rw [term_realize_index, term_realize_index, ← mem_namedGraph_iff hi]
      simp only [show nodeCode indexCode ⟨⟨n, .rel (.named i) ts⟩, v⟩ = codedNode fields v from rfl]
      simp only [fields, follows_codedNode_tag, natCode_inj, Nat.reduceEqDiff, true_and,
        false_and, false_or, or_false]
      change (∃ z ∈ ZFSet.range indexCode, ∃ x ∈ U, ∃ y ∈ U,
        Follows _ (codedNode fields v) z ∧ Argument _ _ _ _ (codedNode fields v) x ∧
        Argument _ _ _ _ (codedNode fields v) y ∧ _) ↔ _
      simp only [hi', h2, h3]
      constructor
      · rintro ⟨z, _, x, _, y, _, hz, hx, hy, h⟩
        change z = indexCode i at hz
        simpa only [← hx, ← hy, hz] using h
      · intro h
        exact ⟨_, ZFSet.mem_range_self i, _, (v (termIndex (ts 0))).property,
          _, (v (termIndex (ts 1))).property, rfl, rfl, rfl, h⟩
  | imp => exact hφ.elim
  | all => exact hφ.elim

end OneYTruth.AtomicTruthFormula


