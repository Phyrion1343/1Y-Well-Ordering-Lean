/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteReflection

/-!
# Textbook finite reflection for the constructible class

This file specializes the Section 6.3 reflection theorem to the transitive
class `L`, following the two-stage proof in Wang Fangting.

First, a finite list of sentences is folded into one conjunction.  The
existing reflection construction selects one constructible level which
contains the transitive seed and is simultaneously absolute with `L` for
every listed sentence and all subformulas needed in the Tarski--Vaught
argument.  Second, the set-sized Skolem/Mostowski theorem is applied inside
that level.  Composing the two equivalences gives a transitive set which is
absolute with the external class `L` for the original finite list and has
the textbook cardinal bound.

This is not full elementarity and does not use the Condensation Lemma.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- A closed tautology, used as the empty conjunction of sentences. -/
def textbookTruthSentence : FOFormula 0 :=
  FOFormula.all (.eq (Fin.last 0) (Fin.last 0))

/-- Right-associated conjunction of a finite sentence list. -/
def textbookSentenceConjunction : List (FOFormula 0) -> FOFormula 0
  | [] => textbookTruthSentence
  | sentence :: rest => .conj sentence (textbookSentenceConjunction rest)

/-- Closure of the folded conjunction contains the closure data for each
sentence occurring in the original list. -/
theorem closesFrom_of_mem_textbookSentenceConjunction
    {sentences : List (FOFormula 0)} {sentence : FOFormula 0}
    {alpha beta : Ordinal.{u}}
    (hclose : ClosesFrom (textbookSentenceConjunction sentences) alpha beta)
    (hsentence : sentence ∈ sentences) :
    ClosesFrom sentence alpha beta := by
  induction sentences with
  | nil => simp at hsentence
  | cons head rest ih =>
      change
        ClosesFrom head alpha beta ∧
          ClosesFrom (textbookSentenceConjunction rest) alpha beta at hclose
      rw [List.mem_cons] at hsentence
      rcases hsentence with rfl | hsentence
      · exact hclose.1
      · exact ih hclose.2 hsentence

/-- A finite sentence list reflects simultaneously between one arbitrarily
high constructible level and the full class `L`. -/
theorem exists_LStage_reflecting_sentenceList
    (sentences : List (FOFormula 0)) (start : Ordinal.{u}) :
    ∃ beta : Ordinal.{u},
      start ≤ beta ∧ Order.IsSuccLimit beta ∧
        ∀ sentence : FOFormula 0, sentence ∈ sentences ->
          (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i) ↔
            Model.SatisfiesIn (L : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i)) := by
  let conjunction := textbookSentenceConjunction sentences
  let beta := reflectionOrdinal conjunction start
  refine ⟨beta, le_reflectionOrdinal conjunction start,
    reflectionOrdinal_isSuccLimit conjunction start, ?_⟩
  intro sentence hsentence
  apply satisfiesIn_stage_iff_L_of_closes sentence beta
  · exact closesFrom_of_mem_textbookSentenceConjunction
      (closesFrom_reflectionOrdinal conjunction start) hsentence
  · exact fun i => Fin.elim0 i

/-- A common reflecting level can also be chosen to contain every member of
a displayed set of constructible parameters. -/
theorem exists_LStage_reflecting_sentenceList_containing
    (sentences : List (FOFormula 0)) (seed : ZFSet.{u})
    (hseedL : ∀ x ∈ seed, x ∈ L) :
    ∃ beta : Ordinal.{u},
      seed ⊆ LStageZF beta ∧ Order.IsSuccLimit beta ∧
        ∀ sentence : FOFormula 0, sentence ∈ sentences ->
          (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i) ↔
            Model.SatisfiesIn (L : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i)) := by
  rcases exists_LStage_for_members hseedL with ⟨alpha, hseedAlpha⟩
  let start : Ordinal.{u} := max alpha (Order.succ 0)
  rcases exists_LStage_reflecting_sentenceList sentences start with
    ⟨beta, hstartBeta, hbetaLimit, hreflect⟩
  refine ⟨beta, ?_, hbetaLimit, hreflect⟩
  intro x hxSeed
  exact LStageZF_mono
    ((le_max_left alpha (Order.succ 0)).trans hstartBeta)
    (hseedAlpha x hxSeed)

/-- The reflecting level chosen above is nonempty; concretely it contains
the empty set already present at level `L_1`. -/
theorem nonempty_LStage_of_succ_zero_le
    {beta : Ordinal.{u}} (hbeta : Order.succ (0 : Ordinal.{u}) ≤ beta) :
    Nonempty (ZFCarrier (LStageZF beta)) := by
  have hemptyOne : (∅ : ZFSet.{u}) ∈
      LStageZF (Order.succ (0 : Ordinal.{u})) := by
    simpa only [LStageZF_zero] using
      (LStageZF_mem_succ (0 : Ordinal.{u}))
  exact ⟨⟨∅, LStageZF_mono hbeta hemptyOne⟩⟩

/--
Wang's Section 6.3, Theorem 3 specialized to `T = L`.

For every finite list of sentences and every transitive set whose members are
constructible, there is a transitive set containing the seed, agreeing with
`L` on each listed sentence, and having cardinality at most
`max aleph0 (card seed)`.
-/
theorem exists_transitive_textbookFiniteFragmentReflection_L
    (sentences : List (FOFormula 0)) (seed : ZFSet.{u})
    (hseedTransitive : seed.IsTransitive)
    (hseedL : ∀ x ∈ seed, x ∈ L) :
    ∃ z : ZFSet.{u},
      seed ⊆ z ∧ z.IsTransitive ∧
        (∀ sentence : FOFormula 0, sentence ∈ sentences ->
          (Model.SatisfiesIn (z : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i) ↔
            Model.SatisfiesIn (L : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i))) ∧
        ZFSet.card z ≤ max Cardinal.aleph0 (ZFSet.card seed) := by
  rcases exists_LStage_for_members hseedL with ⟨alpha, hseedAlpha⟩
  let start : Ordinal.{u} := max alpha (Order.succ 0)
  rcases exists_LStage_reflecting_sentenceList sentences start with
    ⟨beta, hstartBeta, _hbetaLimit, hreflect⟩
  have hseedBeta : seed ⊆ LStageZF beta := by
    intro x hxSeed
    exact LStageZF_mono
      ((le_max_left alpha (Order.succ 0)).trans hstartBeta)
      (hseedAlpha x hxSeed)
  have honeBeta : Order.succ (0 : Ordinal.{u}) ≤ beta :=
    (le_max_right alpha (Order.succ 0)).trans hstartBeta
  let seedIn : ZFSubset (LStageZF beta) := ⟨seed, hseedBeta⟩
  rcases exists_transitive_textbookFiniteFragmentReflection
      (LStageZF beta) (LStageZF_isTransitive beta)
      (nonempty_LStage_of_succ_zero_le honeBeta)
      sentences seedIn hseedTransitive with
    ⟨z, hseedZ, hzTransitive, hzStage, hzCard⟩
  refine ⟨z, hseedZ, hzTransitive, ?_, hzCard⟩
  intro sentence hsentence
  exact (hzStage sentence hsentence).trans
    (hreflect sentence hsentence)

end

end Constructible
