/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomain
public import Mathlib.Data.Fin.VecNotation

/-!
# The parameterized domain of the textbook enumeration recursion

The recursion defining `E(a,n,m)` has one fixed set parameter `a`, whereas
its domain `omega x omega` and its recursion relation do not depend on `a`.
This file inserts the parameter into the first-order contexts by a literal
renaming of the parameter-free formulas from `TextbookEDomain`.

The layouts are

* `(a,key)` for `textbookEDomainWithParamFormula`, and
* `(a,left,right)` for `textbookERelationWithParamFormula`.

In particular, coordinate zero is deliberately absent from both renaming
maps.  No property of `a` is added to either formula.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace TextbookEFormula

/-! ## The formulas and their exact renaming semantics -/

/-- Insert a dummy parameter before the sole domain variable. -/
def textbookEDomainWithParamRename : Fin 1 -> Fin 2 :=
  ![(1 : Fin 2)]

/-- Insert a dummy parameter before the two relation variables. -/
def textbookERelationWithParamRename : Fin 2 -> Fin 3 :=
  ![(1 : Fin 3), (2 : Fin 3)]

/-- The domain formula in the layout `(a,key)`.  The parameter `a` is
syntactically ignored. -/
def textbookEDomainWithParamFormula : FOFormula 2 :=
  FOFormula.rename textbookEDomainWithParamRename domainFormula

/-- The relation formula in the layout `(a,left,right)`.  The parameter `a`
is syntactically ignored. -/
def textbookERelationWithParamFormula : FOFormula 3 :=
  FOFormula.rename textbookERelationWithParamRename relationFormula

@[simp]
theorem textbookEDomainWithParamRename_apply
    (i : Fin 1) : textbookEDomainWithParamRename i = (1 : Fin 2) := by
  fin_cases i
  rfl

@[simp]
theorem textbookERelationWithParamRename_zero :
    textbookERelationWithParamRename (0 : Fin 2) = (1 : Fin 3) := by
  rfl

@[simp]
theorem textbookERelationWithParamRename_one :
    textbookERelationWithParamRename (1 : Fin 2) = (2 : Fin 3) := by
  rfl

/-- Ambient satisfaction of the parameterized domain formula is exactly
ambient satisfaction of the old formula at `key`. -/
@[simp]
theorem satisfies_textbookEDomainWithParamFormula
    (s : Tuple ZFSet.{u} 2) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookEDomainWithParamFormula s <->
      FOFormula.Satisfies Delta0Formula.ZFMem domainFormula ![s 1] := by
  rw [textbookEDomainWithParamFormula, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (textbookEDomainWithParamRename i)) = ![s 1] := by
    funext i
    fin_cases i
    rfl
  rw [hassignment]

/-- Ambient satisfaction of the parameterized relation formula is exactly
ambient satisfaction of the old formula at `(left,right)`. -/
@[simp]
theorem satisfies_textbookERelationWithParamFormula
    (s : Tuple ZFSet.{u} 3) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookERelationWithParamFormula s <->
      FOFormula.Satisfies Delta0Formula.ZFMem relationFormula
        ![s 1, s 2] := by
  rw [textbookERelationWithParamFormula, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (textbookERelationWithParamRename i)) =
        ![s 1, s 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

end TextbookEFormula

namespace Model

/-! ## Restricted semantics and absoluteness -/

private theorem satisfiesIn_rename_iff
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s <->
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-- Restricted satisfaction also forgets precisely the first coordinate. -/
@[simp]
theorem satisfiesIn_textbookEDomainWithParamFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 2) :
    SatisfiesIn M TextbookEFormula.textbookEDomainWithParamFormula s <->
      SatisfiesIn M TextbookEFormula.domainFormula ![s 1] := by
  rw [TextbookEFormula.textbookEDomainWithParamFormula,
    satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s (TextbookEFormula.textbookEDomainWithParamRename i)) =
        ![s 1] := by
    funext i
    fin_cases i
    rfl
  rw [hassignment]

/-- Restricted satisfaction of the relation formula likewise forgets
precisely the first coordinate. -/
@[simp]
theorem satisfiesIn_textbookERelationWithParamFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 3) :
    SatisfiesIn M TextbookEFormula.textbookERelationWithParamFormula s <->
      SatisfiesIn M TextbookEFormula.relationFormula ![s 1, s 2] := by
  rw [TextbookEFormula.textbookERelationWithParamFormula,
    satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s (TextbookEFormula.textbookERelationWithParamRename i)) =
        ![s 1, s 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

/-- In a transitive ZF model, the parameterized class formula has exactly
the textbook domain semantics.  Membership of `a` is recorded because this
is the one-parameter context used by internal recursion; the proof does not
inspect `a`. -/
theorem satisfiesIn_textbookEDomainWithParamFormula_iff
    {M a key : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (_ha : a ∈ M) (hkey : key ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookEFormula.textbookEDomainWithParamFormula ![a, key] <->
      key ∈ TextbookEDomain := by
  rw [satisfiesIn_textbookEDomainWithParamFormula_rename]
  exact satisfiesIn_textbookEDomainFormula_iff hM hkey

/-- In a transitive ZF model, the parameterized relation formula has exactly
the textbook recursion-relation semantics.  It is independent of `a`. -/
theorem satisfiesIn_textbookERelationWithParamFormula_iff
    {M a left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (_ha : a ∈ M) (hleft : left ∈ M) (hright : right ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookEFormula.textbookERelationWithParamFormula
        ![a, left, right] <->
      ClassRel TextbookERelation left right := by
  rw [satisfiesIn_textbookERelationWithParamFormula_rename]
  exact satisfiesIn_textbookERelationFormula_iff hM hleft hright

/-- The model verifies set-likeness for the one-parameter presentation.
This is exactly the already proved parameter-free assertion with a dummy
coordinate inserted; it makes no internal well-foundedness claim. -/
theorem satisfiesIn_textbookESetLikeRelationOnFormula_withParam
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (_ha : a ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula)
      ![a] := by
  rw [satisfiesIn_setLikeRelationOnFormula_iff]
  have hbase := satisfiesIn_textbookESetLikeRelationOnFormula hM
  rw [satisfiesIn_setLikeRelationOnFormula_iff] at hbase
  have hparamOne (parameter x : ZFSet.{u}) :
      snoc ![parameter] x = ![parameter, x] := by
    funext i
    fin_cases i <;> rfl
  have hparamTwo (parameter left right : ZFSet.{u}) :
      snoc (snoc ![parameter] left) right =
        ![parameter, left, right] := by
    funext i
    fin_cases i <;> rfl
  have hparamTwoAfterNormalization
      (parameter left right : ZFSet.{u}) :
      snoc ![parameter, left] right = ![parameter, left, right] := by
    funext i
    fin_cases i <;> rfl
  have hparamOne_key (parameter key : ZFSet.{u}) :
      ![parameter, key] (1 : Fin 2) = key := by
    rfl
  have hparamTwo_left (parameter left right : ZFSet.{u}) :
      ![parameter, left, right] (1 : Fin 3) = left := by
    rfl
  have hparamTwo_right (parameter left right : ZFSet.{u}) :
      ![parameter, left, right] (2 : Fin 3) = right := by
    rfl
  have hzeroOne (x : ZFSet.{u}) :
      snoc (![] : Tuple ZFSet.{u} 0) x = ![x] := by
    funext i
    fin_cases i
    rfl
  have hzeroTwo (left right : ZFSet.{u}) :
      snoc (snoc (![] : Tuple ZFSet.{u} 0) left) right =
        ![left, right] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hparamOne, hparamTwo, hparamTwoAfterNormalization,
    hparamOne_key, hparamTwo_left, hparamTwo_right,
    hzeroOne, hzeroTwo,
    satisfiesIn_textbookEDomainWithParamFormula_rename,
    satisfiesIn_textbookERelationWithParamFormula_rename] using hbase

end Model

end

end Constructible
