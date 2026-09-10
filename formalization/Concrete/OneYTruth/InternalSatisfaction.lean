import OneYTruth.InternalEvaluationFamily
import OneYTruth.EvaluationConvergence
import OneYTruth.ScopedConnectives

/-!
# Internal satisfaction of a fixed smaller set structure

Given the actual canonical diagram sets inside a transitive ambient model,
ordinary expanded Separation constructs the complete satisfaction set by
eventual finite evaluation. The test is a real formula and all finite
history witnesses have already been constructed internally. The ambient
domain is never silently identified with the smaller interpreted domain.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF FormulaCode SyntaxDiagram BoundedEvaluation InternalClosure

universe u v w

/-- Parameters are the six diagram sets, omega, zero, and candidate node x. -/
def eventualFormula (k : Nat) (I : Type v) : (language k I).BoundedFormula Empty 9 :=
  ((memAt k I 9 6) ⊓
    ((memAt k I 10 6).imp
      (((memAt k I 9 10) ⊔ (eqAt k I 9 10)).imp
        (((reindexScoped ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11] (historyQuery k I)).imp
          (memAt k I 8 11)).all))).all).ex

noncomputable def eventualParameters (D : Diagram.{u}) (x : ZFSet.{u}) : Fin 9 → ZFSet.{u} :=
  ![D.nodes, D.atoms, D.trueAtoms, D.implications, D.quantified, D.children,
    Ordinal.omega0.toZFSet, ∅, x]

def EventualCriterion (D : Diagram.{u}) (V x : ZFSet.{u}) : Prop :=
  ∃ m : ZFCarrier V, m.val ∈ Ordinal.omega0.toZFSet ∧
    ∀ n : ZFCarrier V, n.val ∈ Ordinal.omega0.toZFSet →
      (m.val ∈ n.val ∨ m.val = n.val) → ∀ S : ZFCarrier V,
        (∃ H B : ZFCarrier V, IsHistory D H.val B.val ∧ ZFSet.pair n.val S.val ∈ H.val) →
          x ∈ S.val

theorem realize_eventualFormula {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (D : Diagram.{u}) (x : ZFSet.{u})
    (p : Fin 9 → ZFCarrier V) (hp : ∀ i, (p i).val = eventualParameters D x i) :
    OneYTruth.realize N (eventualFormula k I) Empty.elim p ↔ EventualCriterion D V x := by
  have hq (m n S : ZFCarrier V) :
      OneYTruth.realize N (historyQuery k I) Empty.elim
        ((Fin.snoc (Fin.snoc (Fin.snoc p m) n) S) ∘ ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11]) ↔
      ∃ H B : ZFCarrier V, IsHistory D H.val B.val ∧ ZFSet.pair n.val S.val ∈ H.val := by
    apply realize_historyQuery hV N hmem D n.val S.val
    intro i
    fin_cases i <;> simp [Function.comp_apply, Fin.snoc, Fin.castLT,
      hp, eventualParameters, queryParameters]
  simp only [eventualFormula, realize_scoped_ex, realize_scoped_inf, realize_scoped_all,
    realize_scoped_imp, realize_scoped_sup, realize_memAt, realize_eqAt, realize_reindexScoped, hq]
  simp [Fin.snoc, Fin.castPred, Fin.castLT, hmem, Constructible.zfCarrierMem,
    hp, eventualParameters, EventualCriterion]

theorem satisfactionSet_eq_filtered_nodes {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) :
    satisfactionSet indexCode M = ZFSet.range
      (fun w : {w : ScopedAssignment (k := k) I U // OneYTruth.realize M w.1.2 Empty.elim w.2} =>
        nodeCode indexCode w.val) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨φ, ⟨v, hv⟩⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨⟨φ, v⟩, hv⟩, h⟩
  · intro hx
    obtain ⟨⟨⟨φ, v⟩, hv⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨φ, ⟨v, hv⟩⟩, h⟩

/-- The actual smaller-domain full satisfaction set belongs to V.
Only the displayed Separation instances are used, besides elementary set closure. -/
theorem satisfactionSet_mem_of_diagram {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    (hStepSep : SeparationInstance N (mixedStepFormula K J))
    (hSatSep : SeparationInstance N (eventualFormula K J))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hOmega : Ordinal.omega0.toZFSet ∈ V)
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hD : ∀ i, parameters (diagram indexCode M) ∅ i ∈ V) : satisfactionSet indexCode M ∈ V := by
  let D := diagram indexCode M
  have hempty : (∅ : ZFSet.{u}) ∈ V := hD 0
  have hNat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩) hOmega
  have hIter (n : Nat) := iterate_mem hV N hmem hStepSep hempty D hD n
  have hH (n : Nat) := finiteHistory_mem hV N hmem hStepSep hpair hUnion hempty hNat D hD n
  have hB (n : Nat) := historyContainer_mem hV N hmem hStepSep hpair hUnion hempty hNat D hD n
  let p : Fin 8 → ZFCarrier V :=
    ![⟨D.nodes, hD 1⟩, ⟨D.atoms, hD 2⟩, ⟨D.trueAtoms, hD 3⟩,
      ⟨D.implications, hD 4⟩, ⟨D.quantified, hD 5⟩, ⟨D.children, hD 6⟩,
      ⟨Ordinal.omega0.toZFSet, hOmega⟩, ⟨∅, hempty⟩]
  rw [satisfactionSet_eq_filtered_nodes]
  apply filtered_range_mem hV N (eventualFormula K J) hSatSep p
    (nodeCode (k := k) (U := U) indexCode)
    (fun z => OneYTruth.realize M z.1.2 Empty.elim z.2) (hD 1)
  intro z hz
  have hp : ∀ i, ((Fin.snoc p ⟨nodeCode indexCode z, hz⟩ : Fin 9 → ZFCarrier V) i).val =
      eventualParameters D (nodeCode indexCode z) i := by
    intro i
    fin_cases i <;> rfl
  rw [realize_eventualFormula hV N hmem D _ _ hp]
  constructor
  · rintro ⟨m, hm, htail⟩
    obtain ⟨a, ha⟩ := (mem_omega_iff_exists_natCode m.val).mp hm
    let b := max a (formulaDepth z.1.2 + 1)
    have hb : formulaDepth z.1.2 + 1 ≤ b := Nat.le_max_right _ _
    have hab : a ≤ b := Nat.le_max_left _ _
    have horder : m.val ∈ (natCode b : ZFSet.{u}) ∨ m.val = natCode b := by
      rw [ha]
      rcases lt_or_eq_of_le hab with hab | hab
      · exact Or.inl ((natCode_mem_natCode_iff a b).mpr hab)
      · exact Or.inr (congrArg natCode hab)
    have hx := htail ⟨natCode b, hNat b⟩
      ((mem_omega_iff_exists_natCode _).mpr ⟨b, rfl⟩) horder ⟨iterate D b, hIter b⟩
      ⟨⟨finiteHistory D b, hH b⟩, ⟨historyContainer D b, hB b⟩,
        finiteHistory_isHistory D b, last_mem_finiteHistory D b⟩
    exact (node_mem_iterate_iff_of_depth hi M z.1.2 z.2 b hb).mp hx
  · intro ht
    let a := formulaDepth z.1.2 + 1
    refine ⟨⟨natCode a, hNat a⟩, (mem_omega_iff_exists_natCode _).mpr ⟨a, rfl⟩, ?_⟩
    intro n hn horder S hcert
    obtain ⟨b, hb⟩ := (mem_omega_iff_exists_natCode n.val).mp hn
    have hab : a ≤ b := by
      rcases horder with hlt | heq
      · rw [hb] at hlt
        exact Nat.le_of_lt ((natCode_mem_natCode_iff a b).mp hlt)
      · rw [hb] at heq
        exact Nat.le_of_eq (natCode_injective heq)
    obtain ⟨H, B, hh, hns⟩ := hcert
    have hbs : ZFSet.pair (natCode b) S.val ∈ H.val := hb ▸ hns
    rw [hh.value_eq_iterate b hbs]
    exact (node_mem_iterate_iff_of_depth hi M z.1.2 z.2 b hab).mpr ht

end OneYTruth
