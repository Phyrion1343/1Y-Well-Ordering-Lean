/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The textbook enumeration of definable relations

This file proves the two directions of Wang, *Axiomatic Set Theory*, Section
6.4, Proposition 2.  For fixed `a` and finite arity `n`, the recursively
constructed function `E(a,n,m)` enumerates exactly `Df(a,n)`:

`Df(a,n) = {E(a,n,m) | m in omega}`.

The proof follows the displayed five-clause definition.  Soundness is strong
induction on the numerical code, and completeness is induction on the finite
closure stages `D(k,a,n)`.  The resulting cardinal bound is an external
cardinal statement.  Internal model closure is treated separately below by
Replacement, rather than inferred from this external enumeration.
-/

@[expose] public section

open Set
open scoped Cardinal

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

private theorem natCode_mem_textbookEOmega_df (n : Nat) :
    (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode (natCode n)).mpr
    ⟨n, rfl⟩

/-! ## Closure properties of `Df(a,n)` -/

theorem textbookDInZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n i j : Nat} (hi : i < n) (hj : j < n) :
    textbookDInZF a n i j ∈ textbookDfZF a n := by
  apply textbookDStageZF_subset_DfZF a 0 n
  rw [textbookDStageZF_zero]
  exact mem_textbookDZeroZF_iff.mpr
    (Or.inl ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩)

theorem textbookDEqZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n i j : Nat} (hi : i < n) (hj : j < n) :
    textbookDEqZF a n i j ∈ textbookDfZF a n := by
  apply textbookDStageZF_subset_DfZF a 0 n
  rw [textbookDStageZF_zero]
  exact mem_textbookDZeroZF_iff.mpr
    (Or.inr ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩)

private theorem textbookDInZF_self_eq_empty
    (a : ZFSet.{u}) {n i : Nat} (hi : i < n) :
    textbookDInZF a n i i = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro graph hgraph
  rcases mem_textbookDInZF_iff.mp hgraph with
    ⟨hspace, _hi, _hi', x, y, hx, hy, hxy⟩
  have hfunc := mem_textbookTupleSpace_iff.mp hspace
  have hindex : (natCode i : ZFSet.{u}) ∈ natCode n :=
    (mem_natCode_iff_exists_fin (natCode i) n).mpr
      ⟨⟨i, hi⟩, rfl⟩
  rcases hfunc.2 (natCode i) hindex with ⟨value, hvalue, hunique⟩
  have hxvalue : x = value := hunique x hx
  have hyvalue : y = value := hunique y hy
  rw [hxvalue, hyvalue] at hxy
  exact ZFSet.mem_irrefl value hxy

/-- The default value used by malformed `E` codes really is a member of every
`Df(a,n)`.  At positive arity it is the false atomic relation `x_i in x_i`;
at arity zero it is obtained by the textbook's exceptional empty projection.
-/
theorem empty_mem_textbookDfZF (a : ZFSet.{u}) (n : Nat) :
    (∅ : ZFSet.{u}) ∈ textbookDfZF a n := by
  by_cases hn : n = 0
  · subst n
    have hfalse : textbookDInZF a 1 0 0 = (∅ : ZFSet.{u}) :=
      textbookDInZF_self_eq_empty a (by omega)
    have hfalseStage : (∅ : ZFSet.{u}) ∈ textbookDStageZF a 0 1 := by
      rw [textbookDStageZF_zero]
      rw [← hfalse]
      exact mem_textbookDZeroZF_iff.mpr
        (Or.inl ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩)
    apply textbookDStageZF_subset_DfZF a 1 0
    apply mem_textbookDStageZF_succ_iff.mpr
    exact Or.inr (Or.inr (Or.inr
      ⟨∅, hfalseStage, textbookExistsProjZF_zero a ∅⟩))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hfalse := textbookDInZF_self_eq_empty a hnpos
    rw [← hfalse]
    exact textbookDInZF_mem_textbookDfZF a hnpos hnpos

theorem textbookDfZF_relativeDifference
    (a : ZFSet.{u}) {n : Nat} {r : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a n) :
    relativeDifferenceZF (ZFSet.funs (natCode n) a) r ∈
      textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inl ⟨r, hk, rfl⟩)

theorem textbookDfZF_intersection
    (a : ZFSet.{u}) {n : Nat} {r t : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a n) (ht : t ∈ textbookDfZF a n) :
    intersectionZF r t ∈ textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨kr, hkr⟩
  rcases mem_textbookDfZF_iff.mp ht with ⟨kt, hkt⟩
  let k := max kr kt
  have hrk : r ∈ textbookDStageZF a k n :=
    textbookDStageZF_mono a (Nat.le_max_left _ _) hkr
  have htk : t ∈ textbookDStageZF a k n :=
    textbookDStageZF_mono a (Nat.le_max_right _ _) hkt
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inr (Or.inl ⟨r, hrk, t, htk, rfl⟩))

theorem textbookDfZF_existsProjection
    (a : ZFSet.{u}) {n : Nat} {r : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a (n + 1)) :
    textbookExistsProjZF a n r ∈ textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inr (Or.inr ⟨r, hk, rfl⟩))

/-! ## Every value of `E` belongs to `Df` -/

/-- Soundness of the textbook enumeration.  The induction hypothesis is
available at every arity because the projection clause refers to row `n+1`.
-/
theorem textbookEZF_mem_textbookDfZF
    (a : ZFSet.{u}) (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ textbookDfZF a n := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases hdecode : textbookEDecode m with
      | none =>
          rw [textbookEZF_eq_empty_of_decode_none a n m hdecode]
          exact empty_mem_textbookDfZF a n
      | some fields =>
          rcases fields with ⟨i, j, tag⟩
          have hfields :=
            (textbookEDecode_eq_some_iff m i j tag).mp hdecode
          rcases hfields with ⟨htag, hcode⟩
          subst m
          rcases (show tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨
              tag = 4 by omega) with htag | htag | htag | htag | htag <;>
            subst tag
          · by_cases hi : i < n
            · by_cases hj : j < n
              · rw [textbookEZF_code_zero a n i j hi hj,
                  textbookDInCodeZF_natCode]
                exact textbookDInZF_mem_textbookDfZF a hi hj
              · rw [textbookEZF_code_zero_eq_empty_of_not_lt_right
                    a n i j hj]
                exact empty_mem_textbookDfZF a n
            · rw [textbookEZF_code_zero_eq_empty_of_not_lt_left
                  a n i j hi]
              exact empty_mem_textbookDfZF a n
          · by_cases hi : i < n
            · by_cases hj : j < n
              · rw [textbookEZF_code_one a n i j hi hj,
                  textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_textbookDfZF a hi hj
              · rw [textbookEZF_code_one_eq_empty_of_not_lt_right
                    a n i j hj]
                exact empty_mem_textbookDfZF a n
            · rw [textbookEZF_code_one_eq_empty_of_not_lt_left
                  a n i j hi]
              exact empty_mem_textbookDfZF a n
          · rw [textbookEZF_code_two]
            exact textbookDfZF_relativeDifference a
              (ih i (textbookECode_index_lt i j 2) n)
          · rw [textbookEZF_code_three]
            exact textbookDfZF_intersection a
              (ih i (textbookECode_index_lt i j 3) n)
              (ih j (by
                exact lt_of_lt_of_le
                  (lt_of_lt_of_le j.lt_two_pow_self
                    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)) (by
                      simp only [textbookECode]
                      have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
                      have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
                      simpa only [Nat.mul_assoc, Nat.mul_comm,
                        Nat.mul_left_comm] using
                        Nat.le_mul_of_pos_left (3 ^ j)
                          (Nat.mul_pos htwo hfive))) n)
          · rw [textbookEZF_code_four, textbookExistsProjCodeZF_natCode]
            exact textbookDfZF_existsProjection a
              (ih i (textbookECode_index_lt i j 4) (n + 1))

/-! ## Every member of `Df` has an `E` code -/

private theorem exists_textbookECode_of_mem_DStage
    (a : ZFSet.{u}) :
    ∀ k n r, r ∈ textbookDStageZF a k n →
      ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  intro k
  induction k with
  | zero =>
      intro n r hr
      rw [textbookDStageZF_zero] at hr
      rcases mem_textbookDZeroZF_iff.mp hr with
        ⟨i, j, hir⟩ | ⟨i, j, hir⟩
      · refine ⟨textbookECode i.1 j.1 0, ?_⟩
        rw [textbookEZF_code_zero a n i.1 j.1 i.2 j.2,
          textbookDInCodeZF_natCode, hir]
      · refine ⟨textbookECode i.1 j.1 1, ?_⟩
        rw [textbookEZF_code_one a n i.1 j.1 i.2 j.2,
          textbookDEqCodeZF_natCode, hir]
  | succ k ih =>
      intro n r hr
      rcases mem_textbookDStageZF_succ_iff.mp hr with
        hr | ⟨t, ht, htr⟩ | ⟨t, ht, v, hv, htvr⟩ |
          ⟨t, ht, htr⟩
      · exact ih n r hr
      · rcases ih n t ht with ⟨i, hi⟩
        refine ⟨textbookECode i 0 2, ?_⟩
        rw [textbookEZF_code_two, hi]
        exact htr
      · rcases ih n t ht with ⟨i, hi⟩
        rcases ih n v hv with ⟨j, hj⟩
        refine ⟨textbookECode i j 3, ?_⟩
        rw [textbookEZF_code_three, hi, hj]
        exact htvr
      · rcases ih (n + 1) t ht with ⟨i, hi⟩
        refine ⟨textbookECode i 0 4, ?_⟩
        rw [textbookEZF_code_four, textbookExistsProjCodeZF_natCode, hi]
        exact htr

/-- Completeness of the textbook enumeration. -/
theorem exists_textbookEZF_eq_of_mem_textbookDfZF
    {a r : ZFSet.{u}} {n : Nat} (hr : r ∈ textbookDfZF a n) :
    ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  exact exists_textbookECode_of_mem_DStage a k n r hk

/-- Exact elementwise form of the textbook identity
`Df(a,n) = {E(a,n,m) | m in omega}`. -/
theorem mem_textbookDfZF_iff_exists_textbookEZF
    {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDfZF a n ↔
      ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  constructor
  · exact exists_textbookEZF_eq_of_mem_textbookDfZF
  · rintro ⟨m, rfl⟩
    exact textbookEZF_mem_textbookDfZF a n m

/-- Set equality version of the textbook identity.  `ZFSet.range` is only an
ambient set presentation here; model membership is proved by Replacement
below. -/
theorem textbookDfZF_eq_range_textbookEZF (a : ZFSet.{u}) (n : Nat) :
    textbookDfZF a n =
      ZFSet.range (fun m : Nat => textbookEZF a (natCode n) (natCode m)) := by
  apply ZFSet.ext
  intro r
  rw [mem_textbookDfZF_iff_exists_textbookEZF, ZFSet.mem_range]

/-! ## The fixed-arity cardinal bound -/

/-- The actual enumeration, packaged with its proof of membership in `Df`. -/
noncomputable def textbookDfEnumerate (a : ZFSet.{u}) (n : Nat) (m : Nat) :
    ZFCarrier (textbookDfZF a n) :=
  ⟨textbookEZF a (natCode n) (natCode m),
    textbookEZF_mem_textbookDfZF a n m⟩

theorem textbookDfEnumerate_surjective (a : ZFSet.{u}) (n : Nat) :
    Function.Surjective (textbookDfEnumerate a n) := by
  intro r
  rcases exists_textbookEZF_eq_of_mem_textbookDfZF r.2 with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  exact hm

/-- The least textbook `E` code of a member of `Df(a,n)`. -/
noncomputable def firstTextbookECode (a : ZFSet.{u}) (n : Nat)
    (r : ZFCarrier (textbookDfZF a n)) : Nat := by
  classical
  exact Nat.find (exists_textbookEZF_eq_of_mem_textbookDfZF r.2)

@[simp]
theorem textbookEZF_firstTextbookECode
    (a : ZFSet.{u}) (n : Nat)
    (r : ZFCarrier (textbookDfZF a n)) :
    textbookEZF a (natCode n) (natCode (firstTextbookECode a n r)) = r.1 := by
  classical
  exact Nat.find_spec (exists_textbookEZF_eq_of_mem_textbookDfZF r.2)

/-- The selected code is the least code enumerating the relation. -/
theorem firstTextbookECode_minimal
    (a : ZFSet.{u}) (n : Nat)
    (r : ZFCarrier (textbookDfZF a n)) {m : Nat}
    (hm : textbookEZF a (natCode n) (natCode m) = r.1) :
    firstTextbookECode a n r ≤ m := by
  classical
  exact Nat.find_min'
    (exists_textbookEZF_eq_of_mem_textbookDfZF r.2) hm

/-- Least occurrence codes distinguish members of `Df(a,n)`. -/
theorem firstTextbookECode_injective (a : ZFSet.{u}) (n : Nat) :
    Function.Injective (firstTextbookECode a n) := by
  intro r t hcode
  apply Subtype.ext
  have h := congrArg
    (fun m : Nat => textbookEZF a (natCode n) (natCode m)) hcode
  simpa only [textbookEZF_firstTextbookECode] using h

/-- Textbook Section 6.4, Proposition 3: for fixed `a,n`, `Df(a,n)` is at
most countable.  This is the actual cardinality of the `ZFSet`, not merely a
statement that some external predicate has an enumeration. -/
theorem card_textbookDfZF_le_aleph0 (a : ZFSet.{u}) (n : Nat) :
    (textbookDfZF a n).card ≤ Cardinal.aleph0 := by
  have hmk : #(ZFCarrier (textbookDfZF a n)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr
      (firstTextbookECode_injective a n).countable
  rw [ZFSet.cardinalMk_coe_sort] at hmk
  exact Cardinal.lift_le_aleph0.mp hmk

/-! ## The internal Replacement range -/

namespace Model

/-- Every standard value of `E` belongs to a transitive ZF model containing
the set parameter.  This is the closure half of the already established
absoluteness theorem for `E`. -/
theorem textbookEZF_natCode_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ M := by
  let input : Tuple ZFSet.{u} 3 := ![a, natCode n, natCode m]
  have hinputM : TupleIn (M : Set ZFSet.{u}) input := by
    intro i
    fin_cases i
    · exact ha
    · exact natCode_mem_of_isTransitiveZFModel hM n
    · exact natCode_mem_of_isTransitiveZFModel hM m
  have hinputDomain : input ∈ TextbookEZFTupleDomain := by
    exact ⟨natCode_mem_textbookEOmega_df n,
      natCode_mem_textbookEOmega_df m⟩
  have hclosed :=
    (textbookEZF_functionAbsoluteTo hM).1 input hinputM hinputDomain
  simpa [input, textbookEZFTupleFunction] using hclosed

/-- The closure half of Textbook Section 6.4, Proposition 4 for `Df`: if `a`
belongs to a transitive set model of ZF, then every standard finite-arity
`Df(a,n)` belongs to that model.

The proof uses the model's Replacement axiom on its internal standard omega.
The ambient separation below is only the extensional description of the
Replacement witness supplied by the model.
-/
theorem textbookDfZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n : Nat) :
    textbookDfZF a n ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natCode_mem_of_isTransitiveZFModel hM n
  have homegaM : (Ordinal.omega0.toZFSet : ZFSet.{u}) ∈ M :=
    omega_toZFSet_mem_of_isTransitiveZFModel hM
  let paramsM : Tuple (ZFCarrier M) 2 :=
    ![⟨a, ha⟩, ⟨natCode n, hnM⟩]
  let omegaM : ZFCarrier M := ⟨Ordinal.omega0.toZFSet, homegaM⟩
  have hparamsVal : zfCarrierTupleVal paramsM = ![a, natCode n] := by
    funext i
    fin_cases i <;> rfl
  have habsolute := textbookEZF_functionAbsoluteTo hM
  have hfun : forall x : ZFCarrier M, x.1 ∈ omegaM.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookEFormula.textbookEZFFormula
          (snoc (snoc (zfCarrierTupleVal paramsM) x.1) y.1) := by
    intro x hxOmega
    let input : Tuple ZFSet.{u} 3 := ![a, natCode n, x.1]
    have hinputM : TupleIn (M : Set ZFSet.{u}) input := by
      intro i
      fin_cases i
      · exact ha
      · exact hnM
      · exact x.2
    have hinputDomain : input ∈ TextbookEZFTupleDomain := by
      exact ⟨natCode_mem_textbookEOmega_df n, hxOmega⟩
    have hvalueM : textbookEZFTupleFunction input ∈ M :=
      habsolute.1 input hinputM hinputDomain
    let valueM : ZFCarrier M :=
      ⟨textbookEZFTupleFunction input, hvalueM⟩
    refine ⟨valueM, ?_, ?_⟩
    · have hgraph :=
        (habsolute.2 input valueM.1 hinputM valueM.2).mpr
          ⟨hinputDomain, rfl⟩
      rw [hparamsVal]
      have hassignment :
          snoc input valueM.1 =
            snoc (snoc ![a, natCode n] x.1) valueM.1 := by
        funext i
        fin_cases i <;> rfl
      change SatisfiesIn (M : Set ZFSet.{u})
        TextbookEFormula.textbookEZFFormula
        (snoc (snoc ![a, natCode n] x.1) valueM.1)
      rw [← hassignment]
      exact hgraph
    · intro other hother
      have hotherGraph :
          SatisfiesIn (M : Set ZFSet.{u})
            TextbookEFormula.textbookEZFFormula
            (snoc input other.1) := by
        rw [hparamsVal] at hother
        have hassignment :
            snoc input other.1 =
              snoc (snoc ![a, natCode n] x.1) other.1 := by
          funext i
          fin_cases i <;> rfl
        rw [hassignment]
        exact hother
      have hspec :=
        (habsolute.2 input other.1 hinputM other.2).mp hotherGraph
      apply Subtype.ext
      exact hspec.2
  let range : ZFSet.{u} := M.sep fun value =>
    exists code : ZFSet.{u}, code ∈ omegaM.1 ∧
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookEFormula.textbookEZFFormula
        (snoc (snoc (zfCarrierTupleVal paramsM) code) value)
  have hRangeM : range ∈ M := by
    exact satisfiesIn_replacementRange_mem_of_isTransitiveZFModel
      hM TextbookEFormula.textbookEZFFormula paramsM omegaM hfun
  have hRangeEq : range = textbookDfZF a n := by
    apply ZFSet.ext
    intro relation
    rw [ZFSet.mem_sep, mem_textbookDfZF_iff_exists_textbookEZF]
    constructor
    · rintro ⟨hrelationM, code, hcodeOmega, hformula⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code).mp
          hcodeOmega with ⟨m, rfl⟩
      refine ⟨m, ?_⟩
      rw [hparamsVal] at hformula
      have hassignment :
          snoc (snoc ![a, natCode n] (natCode m)) relation =
            ![a, natCode n, natCode m, relation] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment] at hformula
      have hsemantic := satisfiesIn_textbookEZFFormula_natCode_iff
        hM ha hrelationM n m
      exact (hsemantic.mp hformula).symm
    · rintro ⟨m, hm⟩
      have hrelationM : relation ∈ M := by
        rw [← hm]
        exact textbookEZF_natCode_mem_of_isTransitiveZFModel hM ha n m
      refine ⟨hrelationM, natCode m, ?_, ?_⟩
      · exact natCode_mem_textbookEOmega_df m
      · rw [hparamsVal]
        apply (satisfiesIn_textbookEZFFormula_natCode_iff
          hM ha hrelationM n m).mpr
        exact hm.symm
  rw [← hRangeEq]
  exact hRangeM

end Model

/-! ## A pure membership-language graph for `Df` -/

namespace TextbookDfFormula

/-- Select `[a,n,omega,relation]` from the context
`[a,n,output,omega,relation]`. -/
def textbookDfRangeParameters : Fin 4 -> Fin 5 :=
  ![(0 : Fin 5), (1 : Fin 5), (3 : Fin 5), (4 : Fin 5)]

/-- Layout `[a,n,output,omega]`.  Every member of `output` is, and only is, a
value `E(a,n,m)` for some `m in omega`. -/
def textbookDfMembersFormula : FOFormula 4 :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last 4) (2 : Fin 4).castSucc)
    (FOFormula.rename textbookDfRangeParameters
      (replacementRangeFormula TextbookEFormula.textbookEZFFormula))

/-- The public graph of the set-coded function `Df`, with layout
`[a,n,output]`.  The existential variable is the internally least inductive
set, and the explicit membership guard makes the graph false unless
`n in omega`. -/
def textbookDfZFFormula : FOFormula 3 :=
  .ex <| .conj
    (Model.standardOmegaAt (Fin.last 3))
    (.conj
      (.mem (1 : Fin 3).castSucc (Fin.last 3))
      textbookDfMembersFormula)

end TextbookDfFormula

/-- The natural set-coded domain of `Df(a,n)`: the second coordinate must be
a member of the actual standard omega. -/
def TextbookDfZFTupleDomain : Set (Tuple ZFSet.{u} 2) :=
  {s | s 1 ∈ textbookEOmegaZF}

/-- Tuple presentation of the totalized set-coded `Df` operation. -/
noncomputable def textbookDfZFTupleFunction
    (s : Tuple ZFSet.{u} 2) : ZFSet.{u} :=
  textbookDfCodeZF (s 0) (s 1)

namespace Model

private theorem satisfiesIn_all_iff_eDf
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_imp_iff_eDf
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s ↔
      (SatisfiesIn M left s -> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

private theorem satisfiesIn_biimp_iff_eDf
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn,
    satisfiesIn_imp_iff_eDf]
  tauto

private theorem satisfiesIn_textbookDfRangeFormula_natCode_iff
    {M a output relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (FOFormula.rename TextbookDfFormula.textbookDfRangeParameters
          (replacementRangeFormula TextbookEFormula.textbookEZFFormula))
        ![a, natCode n, output, Ordinal.omega0.toZFSet, relation] ↔
      ∃ m : Nat,
        textbookEZF a (natCode n) (natCode m) = relation := by
  rw [satisfiesIn_rename]
  have hassignment :
      (fun i => ![a, natCode n, output, Ordinal.omega0.toZFSet,
          relation] (TextbookDfFormula.textbookDfRangeParameters i)) =
        ![a, natCode n, Ordinal.omega0.toZFSet, relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  have hrange := satisfiesIn_replacementRangeFormula
    (M : Set ZFSet.{u}) TextbookEFormula.textbookEZFFormula
      ![a, natCode n] Ordinal.omega0.toZFSet relation
  rw [show ![a, natCode n, Ordinal.omega0.toZFSet, relation] =
      snoc (snoc ![a, natCode n] Ordinal.omega0.toZFSet) relation by
        funext i
        fin_cases i <;> rfl,
    hrange]
  constructor
  · rintro ⟨code, hcodeM, hcodeOmega, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code).mp
        hcodeOmega with ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    exact ((satisfiesIn_textbookEZFFormula_natCode_iff
      hM ha hrelation n m).mp hformula).symm
  · rintro ⟨m, hm⟩
    refine ⟨natCode m, natCode_mem_of_isTransitiveZFModel hM m,
      natCode_mem_textbookEOmega_df m, ?_⟩
    apply (satisfiesIn_textbookEZFFormula_natCode_iff
      hM ha hrelation n m).mpr
    exact hm.symm

private theorem satisfiesIn_textbookDfMemberBiimp_natCode_iff
    {M a output relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (FOFormula.biimp
          (.mem (Fin.last 4) (2 : Fin 4).castSucc)
          (FOFormula.rename TextbookDfFormula.textbookDfRangeParameters
            (replacementRangeFormula
              TextbookEFormula.textbookEZFFormula)))
        ![a, natCode n, output, Ordinal.omega0.toZFSet, relation] ↔
      (relation ∈ output ↔
        ∃ m : Nat,
          textbookEZF a (natCode n) (natCode m) = relation) := by
  rw [satisfiesIn_biimp_iff_eDf]
  change (relation ∈ output ↔ _) ↔ _
  rw [satisfiesIn_textbookDfRangeFormula_natCode_iff
    hM ha hrelation n]

private theorem satisfiesIn_textbookDfMembersFormula_natCode_iff
    {M a output : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (houtput : output ∈ M) (n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDfFormula.textbookDfMembersFormula
        ![a, natCode n, output, Ordinal.omega0.toZFSet] ↔
      output = textbookDfZF a n := by
  rw [TextbookDfFormula.textbookDfMembersFormula,
    satisfiesIn_all_iff_eDf]
  constructor
  · intro hall
    apply ZFSet.ext
    intro relation
    constructor
    · intro hrelationOutput
      have hrelationM : relation ∈ M :=
        hM.1.mem_trans hrelationOutput houtput
      have hbody := hall relation hrelationM
      have hassignment :
          snoc ![a, natCode n, output, Ordinal.omega0.toZFSet] relation =
            ![a, natCode n, output, Ordinal.omega0.toZFSet, relation] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment] at hbody
      have hiff :=
        (satisfiesIn_textbookDfMemberBiimp_natCode_iff
          hM ha hrelationM n).mp hbody
      exact mem_textbookDfZF_iff_exists_textbookEZF.mpr
        (hiff.mp hrelationOutput)
    · intro hrelationDf
      have hDfM : textbookDfZF a n ∈ M :=
        textbookDfZF_mem_of_isTransitiveZFModel hM ha n
      have hrelationM : relation ∈ M :=
        hM.1.mem_trans hrelationDf hDfM
      have hbody := hall relation hrelationM
      have hassignment :
          snoc ![a, natCode n, output, Ordinal.omega0.toZFSet] relation =
            ![a, natCode n, output, Ordinal.omega0.toZFSet, relation] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment] at hbody
      have hiff :=
        (satisfiesIn_textbookDfMemberBiimp_natCode_iff
          hM ha hrelationM n).mp hbody
      exact hiff.mpr
        (mem_textbookDfZF_iff_exists_textbookEZF.mp hrelationDf)
  · intro houtputEq relation hrelationM
    have hassignment :
        snoc ![a, natCode n, output, Ordinal.omega0.toZFSet] relation =
          ![a, natCode n, output, Ordinal.omega0.toZFSet, relation] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment]
    apply (satisfiesIn_textbookDfMemberBiimp_natCode_iff
      hM ha hrelationM n).mpr
    rw [houtputEq, mem_textbookDfZF_iff_exists_textbookEZF]

/-- Exact restricted semantics of the public `Df` graph on standard codes. -/
theorem satisfiesIn_textbookDfZFFormula_natCode_iff
    {M a output : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (houtput : output ∈ M) (n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDfFormula.textbookDfZFFormula
        ![a, natCode n, output] ↔
      output = textbookDfZF a n := by
  rw [TextbookDfFormula.textbookDfZFFormula, SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaM, homegaFormula, hnOmega, hmembers⟩
    have hsM : forall i,
        snoc ![a, natCode n, output] omega i ∈ M := by
      intro i
      fin_cases i
      · exact ha
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact houtput
      · exact homegaM
    have homega : omega = Ordinal.omega0.toZFSet := by
      simpa only [snoc_last] using
        (satisfiesIn_standardOmegaAt_iff hM (Fin.last 3)
          (snoc ![a, natCode n, output] omega) hsM).mp homegaFormula
    subst omega
    have hassignment :
        snoc ![a, natCode n, output] Ordinal.omega0.toZFSet =
          ![a, natCode n, output, Ordinal.omega0.toZFSet] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment] at hmembers
    exact (satisfiesIn_textbookDfMembersFormula_natCode_iff
      hM ha houtput n).mp hmembers
  · intro houtputEq
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaM : omega ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    refine ⟨omega, homegaM, ?_, ?_, ?_⟩
    · have hsM : forall i,
          snoc ![a, natCode n, output] omega i ∈ M := by
        intro i
        fin_cases i
        · exact ha
        · exact natCode_mem_of_isTransitiveZFModel hM n
        · exact houtput
        · exact homegaM
      apply (satisfiesIn_standardOmegaAt_iff hM (Fin.last 3)
        (snoc ![a, natCode n, output] omega) hsM).mpr
      simp only [snoc_last, omega]
    · exact natCode_mem_textbookEOmega_df n
    · have hassignment :
          snoc ![a, natCode n, output] omega =
            ![a, natCode n, output, Ordinal.omega0.toZFSet] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment]
      exact (satisfiesIn_textbookDfMembersFormula_natCode_iff
        hM ha houtput n).mpr houtputEq

/-- Exact restricted semantics on arbitrary set-coded inputs. -/
theorem satisfiesIn_textbookDfZFFormula_iff
    {M a n output : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hn : n ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDfFormula.textbookDfZFFormula ![a, n, output] ↔
      n ∈ textbookEOmegaZF ∧ output = textbookDfCodeZF a n := by
  constructor
  · intro hformula
    have hfullFormula := hformula
    rw [TextbookDfFormula.textbookDfZFFormula, SatisfiesIn] at hformula
    rcases hformula with
      ⟨omega, homegaM, homegaFormula, hnOmega, _hmembers⟩
    have hsM : forall i, snoc ![a, n, output] omega i ∈ M := by
      intro i
      fin_cases i
      · exact ha
      · exact hn
      · exact houtput
      · exact homegaM
    have homega : omega = Ordinal.omega0.toZFSet := by
      simpa only [snoc_last] using
        (satisfiesIn_standardOmegaAt_iff hM (Fin.last 3)
          (snoc ![a, n, output] omega) hsM).mp homegaFormula
    have hnStandard : n ∈ textbookEOmegaZF := by
      change n ∈ omega at hnOmega
      rw [homega] at hnOmega
      exact hnOmega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp
        hnStandard with ⟨k, rfl⟩
    refine ⟨natCode_mem_textbookEOmega_df k, ?_⟩
    rw [textbookDfCodeZF_natCode]
    exact (satisfiesIn_textbookDfZFFormula_natCode_iff
      hM ha houtput k).mp hfullFormula
  · rintro ⟨hnOmega, houtputEq⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp
        hnOmega with ⟨k, rfl⟩
    apply (satisfiesIn_textbookDfZFFormula_natCode_iff
      hM ha houtput k).mpr
    simpa only [textbookDfCodeZF_natCode] using houtputEq

/-- Full absoluteness of the textbook set-coded function `Df(a,n)` to every
transitive set model of ZF. -/
theorem textbookDfCodeZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) TextbookDfZFTupleDomain
      textbookDfZFTupleFunction TextbookDfFormula.textbookDfZFFormula := by
  constructor
  · intro s hsM hsDomain
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode (s 1)).mp
        hsDomain with ⟨n, hn⟩
    have haM : s 0 ∈ M := hsM 0
    change textbookDfCodeZF (s 0) (s 1) ∈ M
    rw [hn, textbookDfCodeZF_natCode]
    exact textbookDfZF_mem_of_isTransitiveZFModel hM haM n
  · intro s output hsM houtput
    have hassignment : snoc s output = ![s 0, s 1, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment]
    have hsemantic := satisfiesIn_textbookDfZFFormula_iff hM
      (hsM 0) (hsM 1) houtput
    simpa only [TextbookDfZFTupleDomain, textbookDfZFTupleFunction,
      Set.mem_ofPred_eq] using hsemantic

end Model

end

end Constructible
