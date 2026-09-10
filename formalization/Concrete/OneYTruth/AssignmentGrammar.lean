import OneYTruth.InternalBoundedIteration
import OneYTruth.InternalCodeUniverse

/-! # A bounded grammar for genuine length-labelled assignment codes

The empty payload has length zero. A constructor prepends an actual domain
element and increments the length. Both directions are proved against the
actual finite sequence encoding, so no arbitrary source set is accepted.
-/

namespace OneYTruth.AssignmentGrammar

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.IndexedSequenceZF ConstructibleCodeUniverse
open ConstructibleBoundedIteration ConstructibleAssignmentCodes InternalNodes

universe u v

def consBody : Delta0Formula 11 :=
  .conj (Delta0Formula.successorAt 6 8)
    (.conj (kuratowskiPairEqAt 7 10 9) (BoundedEvaluation.pairMemAt 4 8 9))

theorem satisfies_consBody (s : Tuple ZFSet.{u} 11) :
    Satisfies ZFMem consBody s ↔ s 6 = insert (s 8) (s 8) ∧
      s 7 = ZFSet.pair (s 10) (s 9) ∧ ZFSet.pair (s 8) (s 9) ∈ s 4 := by
  simp only [consBody, Satisfies, Delta0Formula.satisfies_successorAt,
    satisfies_kuratowskiPairEqAt, BoundedEvaluation.satisfies_pairMemAt]

attribute [irreducible] consBody

def ruleBody : Delta0Formula 8 :=
  .conj (kuratowskiPairEqAt 5 6 7)
    (.disj (.conj (.eq 6 3) (.eq 7 3)) (.boundedEx 2 (.boundedEx 0 (.boundedEx 1 consBody))))

def Rule (B U W S z : ZFSet.{u}) : Prop :=
  ∃ n ∈ W, ∃ p ∈ B, z = ZFSet.pair n p ∧
    ((n = ∅ ∧ p = ∅) ∨ ∃ m ∈ W, ∃ q ∈ B, ∃ a ∈ U,
      n = insert m m ∧ p = ZFSet.pair a q ∧ ZFSet.pair m q ∈ S)

theorem satisfies_ruleBody (B U W S z n p : ZFSet.{u}) :
    Satisfies ZFMem ruleBody ![B, U, W, ∅, S, z, n, p] ↔
      z = ZFSet.pair n p ∧ ((n = ∅ ∧ p = ∅) ∨
        ∃ m ∈ W, ∃ q ∈ B, ∃ a ∈ U,
          n = insert m m ∧ p = ZFSet.pair a q ∧ ZFSet.pair m q ∈ S) := by
  simp only [ruleBody, Satisfies, satisfies_kuratowskiPairEqAt, satisfies_disj, satisfies_consBody]
  simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
  rfl

attribute [irreducible] ruleBody

def ruleFormula : Delta0Formula 6 := .boundedEx 2 (.boundedEx 0 ruleBody)

theorem satisfies_ruleFormula (B U W S z : ZFSet.{u}) :
    Satisfies ZFMem ruleFormula ![B, U, W, ∅, S, z] ↔ Rule B U W S z := by
  have ht (n p : ZFSet.{u}) : snoc (snoc ![B, U, W, ∅, S, z] n) p =
      ![B, U, W, ∅, S, z, n, p] := by funext i; fin_cases i <;> rfl
  simp only [ruleFormula, Satisfies, ht, satisfies_ruleBody]
  simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
  rfl

noncomputable def params (U : LCarrier.{u}) : Tuple LCarrier.{u} 4 :=
  ![codeUniverse U, U, omegaLCarrier, emptyLCarrier]

noncomputable def stages (U : LCarrier.{u}) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (filterStep ruleFormula 0 (params U)) emptyLCarrier

theorem mem_stages_succ_iff (U : LCarrier.{u}) (m : Nat) (z : ZFSet.{u}) :
    z ∈ (stages U (m+1)).val ↔ z ∈ (codeUniverse U).val ∧
      Rule (codeUniverse U).val U.val Ordinal.omega0.toZFSet (stages U m).val z := by
  change z ∈ deltaSep ruleFormula (snoc (fun i => (params U i).val) (stages U m).val)
      (codeUniverse U).val ↔ _
  rw [deltaSep, ZFSet.mem_sep]
  have ht : snoc (snoc (fun i => (params U i).val) (stages U m).val) z =
      ![(codeUniverse U).val, U.val, Ordinal.omega0.toZFSet, ∅, (stages U m).val, z] := by
    funext i; fin_cases i <;> rfl
  rw [ht, satisfies_ruleFormula]

theorem stages_sound (U : LCarrier.{u}) (m : Nat) :
    ∀ z ∈ (stages U m).val, ∃ xs : List (ZFCarrier U.val),
      FiniteSequenceZF.sequenceCode (xs.map Subtype.val) = z := by
  induction m with
  | zero => intro z hz; exact (ZFSet.notMem_empty z hz).elim
  | succ m ih =>
      intro z hz
      obtain ⟨_, n, _, p, _, hzp, hcase⟩ := (mem_stages_succ_iff U m z).mp hz
      rcases hcase with ⟨rfl, rfl⟩ | ⟨j, _, q, _, a, ha, hn, hp, hjq⟩
      · exact ⟨[], by simpa [FiniteSequenceZF.sequenceCode, natCode] using hzp.symm⟩
      · obtain ⟨xs, hx⟩ := ih _ hjq
        have hj : natCode xs.length = j := by
          simpa only [FiniteSequenceZF.sequenceCode, List.length_map] using (ZFSet.pair_inj.mp hx).1
        have hq : listCode (xs.map Subtype.val) = q := (ZFSet.pair_inj.mp hx).2
        refine ⟨⟨a, ha⟩ :: xs, ?_⟩
        simp only [List.map_cons, FiniteSequenceZF.sequenceCode, List.length_cons,
          List.length_map, listCode_cons]
        rw [hq, ← hp, natCode_succ_eq_insert, hj, ← hn]
        exact hzp.symm

theorem stages_complete (U : LCarrier.{u}) (xs : List (ZFCarrier U.val)) :
    FiniteSequenceZF.sequenceCode (xs.map Subtype.val) ∈ (stages U (xs.length+1)).val := by
  have hlist (ys : List (ZFCarrier U.val)) : listCode (ys.map Subtype.val) ∈ (codeUniverse U).val := by
    apply ConstructibleCodeUniverse.listCode_mem
    intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    exact alphabet_mem a.property
  have hcode (ys : List (ZFCarrier U.val)) :
      FiniteSequenceZF.sequenceCode (ys.map Subtype.val) ∈ (codeUniverse U).val :=
    pair_mem (natCode_mem U _) (hlist ys)
  induction xs with
  | nil =>
      apply (mem_stages_succ_iff U 0 _).mpr
      exact ⟨hcode [], ∅, (mem_omega_iff_exists_natCode _).mpr ⟨0, by simp [natCode]⟩,
        ∅, empty_mem U, by simp [FiniteSequenceZF.sequenceCode, natCode], Or.inl ⟨rfl, rfl⟩⟩
  | cons a xs ih =>
      apply (mem_stages_succ_iff U (xs.length+1) _).mpr
      refine ⟨hcode (a :: xs), natCode (xs.length+1),
        (mem_omega_iff_exists_natCode _).mpr ⟨xs.length+1, rfl⟩,
        listCode ((a :: xs).map Subtype.val), hlist (a :: xs), ?_, Or.inr ?_⟩
      · simp only [FiniteSequenceZF.sequenceCode, List.length_map, List.length_cons]
      · exact ⟨natCode xs.length, (mem_omega_iff_exists_natCode _).mpr ⟨xs.length, rfl⟩,
          listCode (xs.map Subtype.val), hlist xs, a.val, a.property,
          natCode_succ_eq_insert xs.length, rfl, by simpa [FiniteSequenceZF.sequenceCode] using ih⟩

noncomputable def allStages (U : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion (ConstructibleBoundedIteration.family ruleFormula 0 (params U) emptyLCarrier)

theorem allStages_eq_sequenceCodes (U : LCarrier.{u}) :
    (allStages U).val = sequenceCodes U.val := by
  let spec := ConstructibleBoundedIteration.family ruleFormula 0 (params U) emptyLCarrier
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hzL := mem_L_of_mem hz (allStages U).property
    obtain ⟨m, hm⟩ := (mem_parametricUniformOmegaUnion_iff spec ⟨z, hzL⟩).mp hz
    exact ZFSet.mem_range.mpr (stages_sound U m z hm)
  · intro hz
    obtain ⟨xs, rfl⟩ := ZFSet.mem_range.mp hz
    have hc := stages_complete U xs
    have hzL := mem_L_of_mem hc (stages U (xs.length+1)).property
    exact (mem_parametricUniformOmegaUnion_iff spec ⟨_, hzL⟩).mpr ⟨xs.length+1, hc⟩

theorem assignmentCodes_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : InternalClosure.HasCollection N) (hSep : InternalClosure.HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (U : LCarrier.{u}) (hU : U.val ∈ V) :
    assignmentCodes U.val ∈ V := by
  rw [assignmentCodes_eq_sequenceCodes, ← allStages_eq_sequenceCodes U]
  have hB := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  apply InternalBoundedIteration.allStages_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    ruleFormula 0 (params U) _ emptyLCarrier hempty
  intro i
  fin_cases i
  · exact hB
  · exact hU
  · exact hOmega
  · exact hempty

end OneYTruth.AssignmentGrammar

#print axioms OneYTruth.AssignmentGrammar.allStages_eq_sequenceCodes
#print axioms OneYTruth.AssignmentGrammar.assignmentCodes_mem
