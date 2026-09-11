/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEParameterizedDomain
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalTextbookRecursion

/-!
# The textbook simultaneous recursion defining `E`

This file constructs the function `E(a,n,m)` from Wang, *Axiomatic Set
Theory*, Section 6.4.  The recursion is performed on the actual set-coded
domain `omega x omega`, with keys ordered as `<m,n>` and with

`<i,k> R <m,n>` exactly when `i in m`.

Consequently the whole row with first coordinate `i` is available when the
value at first coordinate `m` is formed.  In particular, the projection
clause may use `E(a,n+1,i)`.  No external Lean graph is used as an internal
history witness; the object-language representation is supplied below by the
general internal textbook-recursion theorem.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The ambient recursive solution -/

/-- The class solution of the textbook recursion, totalized by the empty set
away from the set-coded domain `omega x omega`. -/
noncomputable def textbookEByKey (a : ZFSet.{u}) : ZFSet.{u} -> ZFSet.{u} :=
  textbookGlobalRecursionFromLocalGraphs
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a)

/-- The constructed function satisfies the exact textbook class-recursion
equation on its declared domain. -/
theorem textbookEByKey_satisfies_classRecursion (a : ZFSet.{u}) :
    SatisfiesTextbookClassRecursion TextbookEDomain TextbookERelation
      textbookERelation_isWellFoundedSetLikeOn.2.2 (textbookEStep a)
      (textbookEByKey a) := by
  exact textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a)

/-- The pointwise recursion equation on a genuine key. -/
theorem textbookEByKey_eq
    (a : ZFSet.{u}) {key : ZFSet.{u}} (hkey : key ∈ TextbookEDomain) :
    textbookEByKey a key =
      textbookEStep a key
        (predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2 key)
          (textbookEByKey a)) := by
  exact textbookEByKey_satisfies_classRecursion a key hkey

/-- Outside `omega x omega`, the totalized recursive solution is empty. -/
@[simp]
theorem textbookEByKey_eq_empty_of_not_mem
    (a key : ZFSet.{u}) (hkey : key ∉ TextbookEDomain) :
    textbookEByKey a key = ∅ := by
  exact textbookGlobalRecursionFromLocalGraphs_eq_empty_of_not_mem
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a) hkey

/-- The textbook argument order is `(a,n,m)`, while the recursion key is
`<m,n>`. -/
noncomputable def textbookEZF
    (a n m : ZFSet.{u}) : ZFSet.{u} :=
  textbookEByKey a (ZFSet.pair m n)

/-! ## Access to earlier rows -/

private theorem natCode_mem_textbookEOmega (n : Nat) :
    (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode (natCode n)).mpr
    ⟨n, rfl⟩

private theorem textbookE_natKey_mem_domain (m n : Nat) :
    ZFSet.pair (natCode m : ZFSet.{u}) (natCode n) ∈ TextbookEDomain := by
  apply mem_textbookEDomain_iff.mpr
  exact ⟨natCode m, natCode_mem_textbookEOmega m,
    natCode n, natCode_mem_textbookEOmega n, rfl⟩

private theorem textbookE_earlierKey_mem_predecessors
    (m n i k : Nat) (hi : i < m) :
    ZFSet.pair (natCode i : ZFSet.{u}) (natCode k) ∈
      displayedPredecessors TextbookEDomain TextbookERelation
        textbookERelation_isWellFoundedSetLikeOn.2.2
        (ZFSet.pair (natCode m) (natCode n)) := by
  apply (displayedPredecessors_spec
    textbookERelation_isWellFoundedSetLikeOn.2.2
    (textbookE_natKey_mem_domain m n)
    (ZFSet.pair (natCode i) (natCode k))).mpr
  constructor
  · exact textbookE_natKey_mem_domain i k
  · rw [classRel_textbookERelation_iff]
    exact ⟨natCode i, natCode k, natCode m, natCode n,
      natCode_mem_textbookEOmega i, natCode_mem_textbookEOmega k,
      natCode_mem_textbookEOmega m, natCode_mem_textbookEOmega n,
      rfl, rfl, (natCode_mem_natCode_iff i m).mpr hi⟩

private theorem uniqueGraphLookupZF_predecessorRestrictionGraph
    (domain : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u})
    {key : ZFSet.{u}} (hkey : key ∈ domain) :
    uniqueGraphLookupZF (predecessorRestrictionGraph domain f) key = f key := by
  apply uniqueGraphLookupZF_eq_of_unique
  · exact pair_mem_predecessorRestrictionGraph f hkey
  · intro other hother
    rcases mem_predecessorRestrictionGraph_iff.mp hother with
      ⟨source, _hsource, hpair⟩
    have hcoordinates := ZFSet.pair_inj.mp hpair
    rw [hcoordinates.1] at hcoordinates
    exact hcoordinates.2.symm

private theorem textbookE_history_lookup
    (a : ZFSet.{u}) (m n i k : Nat) (hi : i < m) :
    uniqueGraphLookupZF
        (predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2
            (ZFSet.pair (natCode m) (natCode n)))
          (textbookEByKey a))
        (ZFSet.pair (natCode i) (natCode k)) =
      textbookEZF a (natCode k) (natCode i) := by
  rw [uniqueGraphLookupZF_predecessorRestrictionGraph _ _
    (textbookE_earlierKey_mem_predecessors m n i k hi)]
  rfl

/-! ## The five equations from Section 6.4 -/

@[simp]
theorem textbookEZF_code_zero
    (a : ZFSet.{u}) (n i j : Nat) (hi : i < n) (hj : j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) =
      textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero a _ n i j hi hj

@[simp]
theorem textbookEZF_code_one
    (a : ZFSet.{u}) (n i j : Nat) (hi : i < n) (hj : j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) =
      textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one a _ n i j hi hj

@[simp]
theorem textbookEZF_code_two
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 2)) =
      relativeDifferenceZF (ZFSet.funs (natCode n) a)
        (textbookEZF a (natCode n) (natCode i)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 2) n),
    textbookEStep_code_two]
  exact congrArg (relativeDifferenceZF (ZFSet.funs (natCode n) a))
    (textbookE_history_lookup a (textbookECode i j 2) n i n
      (textbookECode_index_lt i j 2))

@[simp]
theorem textbookEZF_code_three
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 3)) =
      intersectionZF
        (textbookEZF a (natCode n) (natCode i))
        (textbookEZF a (natCode n) (natCode j)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 3) n),
    textbookEStep_code_three]
  rw [textbookE_history_lookup a (textbookECode i j 3) n i n
      (textbookECode_index_lt i j 3),
    textbookE_history_lookup a (textbookECode i j 3) n j n]
  exact lt_of_lt_of_le
    (lt_of_lt_of_le j.lt_two_pow_self
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)) (by
    simp only [textbookECode]
    have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.le_mul_of_pos_left (3 ^ j) (Nat.mul_pos htwo hfive))

@[simp]
theorem textbookEZF_code_four
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 4)) =
      textbookExistsProjCodeZF a (natCode n)
        (textbookEZF a (natCode (n + 1)) (natCode i)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 4) n),
    textbookEStep_code_four]
  exact congrArg (textbookExistsProjCodeZF a (natCode n))
    (textbookE_history_lookup a (textbookECode i j 4) n i (n + 1)
      (textbookECode_index_lt i j 4))

/-! The dummy field `j` in clauses two and four remains part of the code,
exactly as in the textbook, even though the resulting set does not depend on
that field. -/

@[simp]
theorem textbookEZF_code_zero_eq_empty_of_not_lt_left
    (a : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero_eq_empty_of_not_lt_left a _ n i j hi

@[simp]
theorem textbookEZF_code_zero_eq_empty_of_not_lt_right
    (a : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero_eq_empty_of_not_lt_right a _ n i j hj

@[simp]
theorem textbookEZF_code_one_eq_empty_of_not_lt_left
    (a : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one_eq_empty_of_not_lt_left a _ n i j hi

@[simp]
theorem textbookEZF_code_one_eq_empty_of_not_lt_right
    (a : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one_eq_empty_of_not_lt_right a _ n i j hj

/-- The final "otherwise" branch for a malformed natural-number code. -/
@[simp]
theorem textbookEZF_eq_empty_of_decode_none
    (a : ZFSet.{u}) (n m : Nat) (hm : textbookEDecode m = none) :
    textbookEZF a (natCode n) (natCode m) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain m n)]
  simp [textbookEStep, hm]

/-! ## Pure membership-language graphs -/

namespace TextbookEFormula

/-- The graph of the recursive solution with layout `[a,key,output]`. -/
def textbookERecursionValueFormula : FOFormula 3 :=
  Model.recursionValueFormula textbookEDomainWithParamFormula
    textbookERelationWithParamFormula textbookEStepFormula

/-- Coordinate map selecting `[a,key,output]` from the existential context
`[a,n,m,output,key]`. -/
def textbookERecursionValueParameters : Fin 3 -> Fin 5 :=
  ![(0 : Fin 5), (4 : Fin 5), (3 : Fin 5)]

/-- The public graph of `E`, with layout `[a,n,m,output]`.

The quantified witness is the internal Kuratowski pair `<m,n>`, in the same
order as the ambient recursion key. -/
def textbookEZFFormula : FOFormula 4 :=
  .ex <| .conj
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last 4) (2 : Fin 5) (1 : Fin 5)).toFO
    (FOFormula.rename textbookERecursionValueParameters
      textbookERecursionValueFormula)

@[simp]
theorem textbookERecursionValueParameters_zero :
    textbookERecursionValueParameters (0 : Fin 3) = (0 : Fin 5) := by
  rfl

@[simp]
theorem textbookERecursionValueParameters_one :
    textbookERecursionValueParameters (1 : Fin 3) = (4 : Fin 5) := by
  rfl

@[simp]
theorem textbookERecursionValueParameters_two :
    textbookERecursionValueParameters (2 : Fin 3) = (3 : Fin 5) := by
  rfl

end TextbookEFormula

/-! ## The set-coded input domain -/

/-- Arguments `(a,n,m)` on which `E` is defined: `n` and `m` are members of
the actual standard omega.  The set parameter `a` is unrestricted. -/
def TextbookEZFTupleDomain : Set (Tuple ZFSet.{u} 3) :=
  {s | s 1 ∈ textbookEOmegaZF ∧ s 2 ∈ textbookEOmegaZF}

@[simp]
theorem pair_mem_textbookEDomain_iff
    (m n : ZFSet.{u}) :
    ZFSet.pair m n ∈ TextbookEDomain ↔
      m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF := by
  constructor
  · intro hpair
    rcases mem_textbookEDomain_iff.mp hpair with
      ⟨m', hm', n', hn', hp⟩
    have hcoordinates := ZFSet.pair_inj.mp hp
    simpa only [hcoordinates.1, hcoordinates.2] using And.intro hm' hn'
  · rintro ⟨hm, hn⟩
    exact mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩

/-- Tuple presentation of the textbook function. -/
noncomputable def textbookEZFTupleFunction
    (s : Tuple ZFSet.{u} 3) : ZFSet.{u} :=
  textbookEZF (s 0) (s 1) (s 2)

namespace Model

private theorem satisfiesIn_rename_iff_eRecursion
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s ↔
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

@[simp]
theorem satisfiesIn_textbookERecursionValueFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 5) :
    SatisfiesIn M
        (FOFormula.rename TextbookEFormula.textbookERecursionValueParameters
          TextbookEFormula.textbookERecursionValueFormula) s ↔
      SatisfiesIn M TextbookEFormula.textbookERecursionValueFormula
        ![s 0, s 4, s 3] := by
  rw [satisfiesIn_rename_iff_eRecursion]
  have hassignment :
      (fun i => s
        (TextbookEFormula.textbookERecursionValueParameters i)) =
        ![s 0, s 4, s 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

/-- Absoluteness of the solution as a unary function of the recursion key,
at the fixed set parameter `a`. -/
theorem textbookEByKey_unaryFunctionAbsoluteAt
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M) :
    UnaryFunctionAbsoluteAt (M : Set ZFSet.{u}) ![a]
      TextbookEDomain (textbookEByKey a)
      TextbookEFormula.textbookERecursionValueFormula := by
  have hparams : forall i : Fin 1, ![a] i ∈ M := by
    intro i
    fin_cases i
    exact ha
  have hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u})
          TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a] z) ↔ z ∈ TextbookEDomain) := by
    intro z hzM
    have hs : snoc ![a] z = ![a, z] := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact satisfiesIn_textbookEDomainWithParamFormula_iff hM ha hzM
  have hrelation : forall left, left ∈ M -> forall right, right ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u})
          TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a] left) right) ↔
        ClassRel TextbookERelation left right) := by
    intro left hleftM right hrightM
    have hs : snoc (snoc ![a] left) right = ![a, left, right] := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact satisfiesIn_textbookERelationWithParamFormula_iff
      hM ha hleftM hrightM
  have habsolute := unaryFunctionAbsoluteAt_of_textbookRecursion hM
    TextbookEFormula.textbookEDomainWithParamFormula
    TextbookEFormula.textbookERelationWithParamFormula
    TextbookEFormula.textbookEStepFormula ![a]
    textbookERelation_isWellFoundedSetLikeOn hparams hclass hrelation
    (textbookERelation_predecessorsClosedIn hM)
    (satisfiesIn_textbookESetLikeRelationOnFormula_withParam hM ha)
    (textbookEStep_absoluteAt hM ha)
    (F := textbookEByKey a) (by
      intro key hkey
      exact textbookEByKey_eq a (mem_modelIntersectionZF_iff.mp hkey).2)
  simpa only [TextbookEFormula.textbookERecursionValueFormula] using habsolute

/-- Exact restricted semantics of the public graph `[a,n,m,output]`. -/
theorem satisfiesIn_textbookEZFFormula_iff
    {M a n m output : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hn : n ∈ M) (hm : m ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] ↔
      (n ∈ textbookEOmegaZF ∧ m ∈ textbookEOmegaZF) ∧
        output = textbookEZF a n m := by
  have habsolute := textbookEByKey_unaryFunctionAbsoluteAt hM ha
  rw [TextbookEFormula.textbookEZFFormula, SatisfiesIn]
  constructor
  · rintro ⟨key, hkeyM, hpairFormula, hrecursionFormula⟩
    have hsM : forall i,
        snoc ![a, n, m, output] key i ∈ M := by
      intro i
      fin_cases i <;> assumption
    have hpair := (satisfiesIn_delta0_iff hM.1
      (Delta0Formula.kuratowskiPairEqAt
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5))
      (snoc ![a, n, m, output] key) hsM).mp hpairFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt] at hpair
    change key = ZFSet.pair m n at hpair
    have hrecursion :
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookEFormula.textbookERecursionValueFormula
          ![a, key, output] :=
      (satisfiesIn_textbookERecursionValueFormula_rename
        (M : Set ZFSet.{u})
        (snoc ![a, n, m, output] key)).mp hrecursionFormula
    have hassignment : snoc (snoc ![a] key) output =
        ![a, key, output] := by
      funext i
      fin_cases i <;> rfl
    have hgraph := habsolute.2 key output hkeyM houtput
    rw [hassignment] at hgraph
    rcases hgraph.mp hrecursion with ⟨hkeyDomain, hvalue⟩
    subst key
    exact ⟨(pair_mem_textbookEDomain_iff m n).mp hkeyDomain |>.symm,
      by simpa only [textbookEZF] using hvalue⟩
  · rintro ⟨⟨hnOmega, hmOmega⟩, hvalue⟩
    let key : ZFSet.{u} := ZFSet.pair m n
    have hkeyM : key ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM hm hn
    have hkeyDomain : key ∈ TextbookEDomain :=
      (pair_mem_textbookEDomain_iff m n).mpr ⟨hmOmega, hnOmega⟩
    refine ⟨key, hkeyM, ?_, ?_⟩
    · have hsM : forall i,
          snoc ![a, n, m, output] key i ∈ M := by
        intro i
        fin_cases i <;> assumption
      apply (satisfiesIn_delta0_iff hM.1
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last 4) (2 : Fin 5) (1 : Fin 5))
        (snoc ![a, n, m, output] key) hsM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt]
      rfl
    · apply (satisfiesIn_textbookERecursionValueFormula_rename
        (M : Set ZFSet.{u})
        (snoc ![a, n, m, output] key)).mpr
      have hassignment : snoc (snoc ![a] key) output =
          ![a, key, output] := by
        funext i
        fin_cases i <;> rfl
      have hgraph := habsolute.2 key output hkeyM houtput
      rw [hassignment] at hgraph
      apply hgraph.mpr
      exact ⟨hkeyDomain, by simpa only [key, textbookEZF] using hvalue⟩

/-- The exact textbook function on set-coded natural-number inputs is
absolute to every transitive ZF model containing its arguments. -/
theorem textbookEZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) TextbookEZFTupleDomain
      textbookEZFTupleFunction TextbookEFormula.textbookEZFFormula := by
  constructor
  · intro s hsM hsDomain
    have hkeyM : ZFSet.pair (s 2) (s 1) ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM (hsM 2) (hsM 1)
    have hkeyDomain : ZFSet.pair (s 2) (s 1) ∈ TextbookEDomain :=
      (pair_mem_textbookEDomain_iff (s 2) (s 1)).mpr
        ⟨hsDomain.2, hsDomain.1⟩
    exact (textbookEByKey_unaryFunctionAbsoluteAt hM (hsM 0)).1
      (ZFSet.pair (s 2) (s 1)) hkeyM hkeyDomain
  · intro s output hsM houtput
    have hassignment : snoc s output =
        ![s 0, s 1, s 2, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment]
    have hsemantic := satisfiesIn_textbookEZFFormula_iff hM
      (hsM 0) (hsM 1) (hsM 2) houtput
    simpa only [TextbookEZFTupleDomain, textbookEZFTupleFunction,
      Set.mem_ofPred_eq] using hsemantic

/-- Specialization to ordinary metatheoretic naturals. -/
theorem satisfiesIn_textbookEZFFormula_natCode_iff
    {M a output : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (houtput : output ∈ M) (n m : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.textbookEZFFormula
        ![a, natCode n, natCode m, output] ↔
      output = textbookEZF a (natCode n) (natCode m) := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natCode_mem_of_isTransitiveZFModel hM n
  have hmM : (natCode m : ZFSet.{u}) ∈ M :=
    natCode_mem_of_isTransitiveZFModel hM m
  rw [satisfiesIn_textbookEZFFormula_iff hM ha hnM hmM houtput]
  simp only [natCode_mem_textbookEOmega, true_and]

end Model

end

end Constructible
