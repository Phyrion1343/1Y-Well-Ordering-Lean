/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookTupleSpaceAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula

/-!
# The well-founded domain for the textbook enumeration of definable sets

For the simultaneous recursion defining `E(a,n,m)`, the recursion domain is
the actual set `omega x omega` of Kuratowski pairs.  The relation ignores the
second coordinate:

`<i,k> R <m,n>` if and only if `i in m`.

Both the domain and the relation below are expressed by parameter-free
formulas in the pure membership language.  In particular, the external Lean
type `Nat x Nat` is used only as a proof device for well-foundedness; it is
never used as the set-theoretic recursion domain.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The actual set-coded domain and relation -/

/-- The standard von Neumann omega, used in the set-coded recursion domain. -/
abbrev textbookEOmegaZF : ZFSet.{u} := Ordinal.omega0.toZFSet

/-- The actual set of Kuratowski codes `<m,n>` with `m,n in omega`. -/
def textbookEDomainZF : ZFSet.{u} :=
  ZFSet.prod textbookEOmegaZF textbookEOmegaZF

/-- The recursion domain as the external class represented by
`textbookEDomainZF`. -/
def TextbookEDomain : Set ZFSet.{u} :=
  (textbookEDomainZF : Set ZFSet.{u})

/-- The recursion relation on set-coded pairs.  Both arguments are required
to be genuine pairs of standard finite ordinals. -/
def TextbookERelation : Set (Tuple ZFSet.{u} 2) :=
  {s | exists i k m n : ZFSet.{u},
    i ∈ textbookEOmegaZF ∧ k ∈ textbookEOmegaZF ∧
    m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF ∧
    s 0 = ZFSet.pair i k ∧ s 1 = ZFSet.pair m n ∧ i ∈ m}

@[simp]
theorem mem_textbookEDomain_iff {x : ZFSet.{u}} :
    x ∈ TextbookEDomain ↔
      exists m : ZFSet.{u}, m ∈ textbookEOmegaZF ∧
        exists n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
          x = ZFSet.pair m n := by
  exact ZFSet.mem_prod

@[simp]
theorem classRel_textbookERelation_iff
    (left right : ZFSet.{u}) :
    ClassRel TextbookERelation left right ↔
      exists i k m n : ZFSet.{u},
        i ∈ textbookEOmegaZF ∧ k ∈ textbookEOmegaZF ∧
        m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF ∧
        left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m := by
  rfl

/-! ## Pure membership-language formulas -/

namespace TextbookEFormula

/-- With coordinates `(left,right,omega)`, the bounded formula saying that
`left = <i,k>`, `right = <m,n>`, and `i in m`, for four coordinates bounded
by `omega`. -/
def relationDeltaAt {n : Nat}
    (left right omega : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx omega
    (Delta0Formula.boundedEx omega.castSucc
      (Delta0Formula.boundedEx omega.castSucc.castSucc
        (Delta0Formula.boundedEx omega.castSucc.castSucc.castSucc
          (.conj
            (Delta0Formula.kuratowskiPairEqAt
              left.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                right.castSucc.castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc
                (Fin.last (n + 3)))
              (.mem
                (Fin.last n).castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc))))))

@[simp]
theorem satisfies_relationDeltaAt {n : Nat}
    (left right omega : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (relationDeltaAt left right omega) s ↔
      exists i : ZFSet.{u}, i ∈ s omega ∧
        exists k : ZFSet.{u}, k ∈ s omega ∧
          exists m : ZFSet.{u}, m ∈ s omega ∧
            exists next : ZFSet.{u}, next ∈ s omega ∧
              s left = ZFSet.pair i k ∧
              s right = ZFSet.pair m next ∧ i ∈ m := by
  simp [relationDeltaAt]

/-- Parameter-free formula for membership in the set-coded domain
`omega x omega`. -/
def domainFormula : FOFormula 1 :=
  .ex (.conj
    (Model.standardOmegaAt (Fin.last 1))
    (TextbookDefFormula.productMemberDeltaAt
      (0 : Fin 2) (Fin.last 1) (Fin.last 1)).toFO)

/-- Parameter-free formula for the relation `<i,k> R <m,n>` iff `i in m`. -/
def relationFormula : FOFormula 2 :=
  .ex (.conj
    (Model.standardOmegaAt (Fin.last 2))
    (relationDeltaAt (0 : Fin 3) (1 : Fin 3) (Fin.last 2)).toFO)

end TextbookEFormula

namespace Model

noncomputable section

/-! ## Exact restricted semantics and absoluteness -/

theorem satisfiesIn_textbookEDomainFormula_iff
    {M x : ZFSet.{u}} (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.domainFormula ![x] ↔
      x ∈ TextbookEDomain := by
  simp only [TextbookEFormula.domainFormula, SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaM, homegaFormula, hxProductFormula⟩
    have homega : omega = textbookEOmegaZF := by
      apply (satisfiesIn_standardOmegaAt_iff hM (Fin.last 1)
        ![x, omega] (by
          intro i
          fin_cases i
          · exact hx
          · exact homegaM)).mp
      exact homegaFormula
    have hs : forall i : Fin 2, ![x, omega] i ∈ M := by
      intro i
      fin_cases i
      · exact hx
      · exact homegaM
    have hdelta := (satisfiesIn_delta0_iff hM.1
      (TextbookDefFormula.productMemberDeltaAt
        (0 : Fin 2) (Fin.last 1) (Fin.last 1))
      ![x, omega] hs).mp hxProductFormula
    have hxProduct : x ∈ ZFSet.prod omega omega := by
      simpa using hdelta
    change x ∈ textbookEDomainZF
    simpa only [textbookEDomainZF, homega] using hxProduct
  · intro hxDomain
    let omega : ZFSet.{u} := textbookEOmegaZF
    have homegaM : omega ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    refine ⟨omega, homegaM, ?_, ?_⟩
    · apply (satisfiesIn_standardOmegaAt_iff hM (Fin.last 1)
        ![x, omega] (by
          intro i
          fin_cases i
          · exact hx
          · exact homegaM)).mpr
      rfl
    · have hs : forall i : Fin 2, ![x, omega] i ∈ M := by
        intro i
        fin_cases i
        · exact hx
        · exact homegaM
      apply (satisfiesIn_delta0_iff hM.1
        (TextbookDefFormula.productMemberDeltaAt
          (0 : Fin 2) (Fin.last 1) (Fin.last 1))
        ![x, omega] hs).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_productMemberDeltaAt]
      change x ∈ ZFSet.prod omega omega
      change x ∈ textbookEDomainZF at hxDomain
      simpa only [textbookEDomainZF, omega] using hxDomain

theorem satisfiesIn_textbookERelationFormula_iff
    {M left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.relationFormula
        ![left, right] ↔
      ClassRel TextbookERelation left right := by
  simp only [TextbookEFormula.relationFormula, SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaM, homegaFormula, hrelationFormula⟩
    have homega : omega = textbookEOmegaZF := by
      apply (satisfiesIn_standardOmegaAt_iff hM (Fin.last 2)
        ![left, right, omega] (by
          intro i
          fin_cases i
          · exact hleft
          · exact hright
          · exact homegaM)).mp
      exact homegaFormula
    have hs : forall i : Fin 3, ![left, right, omega] i ∈ M := by
      intro i
      fin_cases i
      · exact hleft
      · exact hright
      · exact homegaM
    have hdelta := (satisfiesIn_delta0_iff hM.1
      (TextbookEFormula.relationDeltaAt
        (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
      ![left, right, omega] hs).mp hrelationFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookEFormula.satisfies_relationDeltaAt] at hdelta
    change exists i, i ∈ omega ∧
      exists k, k ∈ omega ∧
        exists m, m ∈ omega ∧
          exists n, n ∈ omega ∧
            left = ZFSet.pair i k ∧
            right = ZFSet.pair m n ∧ i ∈ m at hdelta
    rcases hdelta with
      ⟨i, hi, k, hk, m, hm, n, hn, hleftPair, hrightPair, him⟩
    rw [classRel_textbookERelation_iff]
    exact ⟨i, k, m, n, by simpa only [homega] using hi,
      by simpa only [homega] using hk,
      by simpa only [homega] using hm,
      by simpa only [homega] using hn,
      hleftPair, hrightPair, him⟩
  · intro hrelation
    let omega : ZFSet.{u} := textbookEOmegaZF
    have homegaM : omega ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    refine ⟨omega, homegaM, ?_, ?_⟩
    · apply (satisfiesIn_standardOmegaAt_iff hM (Fin.last 2)
        ![left, right, omega] (by
          intro i
          fin_cases i
          · exact hleft
          · exact hright
          · exact homegaM)).mpr
      rfl
    · have hs : forall i : Fin 3, ![left, right, omega] i ∈ M := by
        intro i
        fin_cases i
        · exact hleft
        · exact hright
        · exact homegaM
      apply (satisfiesIn_delta0_iff hM.1
        (TextbookEFormula.relationDeltaAt
          (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
        ![left, right, omega] hs).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookEFormula.satisfies_relationDeltaAt]
      change exists i, i ∈ omega ∧
        exists k, k ∈ omega ∧
          exists m, m ∈ omega ∧
            exists n, n ∈ omega ∧
              left = ZFSet.pair i k ∧
              right = ZFSet.pair m n ∧ i ∈ m
      rw [classRel_textbookERelation_iff] at hrelation
      rcases hrelation with
        ⟨i, k, m, n, hi, hk, hm, hn, hleftPair, hrightPair, him⟩
      exact ⟨i, by simpa only [omega] using hi,
        k, by simpa only [omega] using hk,
        m, by simpa only [omega] using hm,
        n, by simpa only [omega] using hn,
        hleftPair, hrightPair, him⟩

theorem textbookEDomain_classAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    ClassAbsoluteTo (M : Set ZFSet.{u}) TextbookEDomain
      TextbookEFormula.domainFormula := by
  intro x hx
  exact satisfiesIn_textbookEDomainFormula_iff hM hx

theorem textbookERelation_relationAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    RelationAbsoluteTo (M : Set ZFSet.{u}) TextbookERelation
      TextbookEFormula.relationFormula := by
  intro s hs
  have h0 : s 0 ∈ M := hs 0
  have h1 : s 1 ∈ M := hs 1
  have hassignment : s = ![s 0, s 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  exact satisfiesIn_textbookERelationFormula_iff hM h0 h1

end

end Model

/-! ## Exact predecessor sets and well-foundedness -/

theorem mem_textbookEOmega_of_mem_of_mem_textbookEOmega
    {i m : ZFSet.{u}} (hi : i ∈ m) (hm : m ∈ textbookEOmegaZF) :
    i ∈ textbookEOmegaZF := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨a, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt i a).mp hi with
    ⟨b, _hb, rfl⟩
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode b)).mpr ⟨b, rfl⟩

/-- At the key `<m,n>`, the full predecessor class is the actual set
`m x omega`. -/
theorem textbookE_predecessorSet
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    IsPredecessorSet TextbookEDomain TextbookERelation
      (ZFSet.pair m n) (ZFSet.prod m textbookEOmegaZF) := by
  intro y
  constructor
  · intro hy
    rcases ZFSet.mem_prod.mp hy with ⟨i, hi, k, hk, rfl⟩
    have hiOmega : i ∈ textbookEOmegaZF :=
      mem_textbookEOmega_of_mem_of_mem_textbookEOmega hi hm
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨i, hiOmega, k, hk, rfl⟩
    · rw [classRel_textbookERelation_iff]
      exact ⟨i, k, m, n, hiOmega, hk, hm, hn, rfl, rfl, hi⟩
  · rintro ⟨_hyDomain, hyRelation⟩
    rw [classRel_textbookERelation_iff] at hyRelation
    rcases hyRelation with
      ⟨i, k, m', n', hiOmega, hk, _hm', _hn',
        hyPair, hkeyPair, him'⟩
    have hcoordinates := ZFSet.pair_inj.mp hkeyPair
    have him : i ∈ m := by
      simpa only [hcoordinates.1] using him'
    exact ZFSet.mem_prod.mpr ⟨i, him, k, hk, hyPair⟩

/-- Every element of the domain has a unique pair of standard natural-number
coordinates.  This lemma is used only to define an external well-founded
measure. -/
private theorem exists_textbookENatCode
    (x : ZFCarrier textbookEDomainZF.{u}) :
    exists code : Nat × Nat,
      x.1 = ZFSet.pair (natCode code.1) (natCode code.2) := by
  rcases ZFSet.mem_prod.mp x.2 with ⟨m, hm, n, hn, hx⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨a, rfl⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp hn with
    ⟨b, rfl⟩
  exact ⟨(a, b), hx⟩

/-- External decoding of a genuine set-coded key. -/
private noncomputable def textbookENatCode
    (x : ZFCarrier textbookEDomainZF.{u}) : Nat × Nat :=
  Classical.choose (exists_textbookENatCode x)

private theorem textbookENatCode_spec
    (x : ZFCarrier textbookEDomainZF.{u}) :
    x.1 = ZFSet.pair (natCode (textbookENatCode x).1)
      (natCode (textbookENatCode x).2) :=
  Classical.choose_spec (exists_textbookENatCode x)

private theorem textbookENatCode_first_lt_of_relation
    {left right : ZFCarrier textbookEDomainZF.{u}}
    (h : ClassRel TextbookERelation.{u} left.1 right.1) :
    (textbookENatCode left).1 < (textbookENatCode right).1 := by
  rw [classRel_textbookERelation_iff] at h
  rcases h with
    ⟨i, k, m, n, _hiOmega, _hk, _hm, _hn,
      hleft, hright, him⟩
  have hleftCoordinates := ZFSet.pair_inj.mp
    ((textbookENatCode_spec left).symm.trans hleft)
  have hrightCoordinates := ZFSet.pair_inj.mp
    ((textbookENatCode_spec right).symm.trans hright)
  have hcodes :
      (natCode (textbookENatCode left).1 : ZFSet.{u}) ∈
        natCode (textbookENatCode right).1 := by
    rw [hleftCoordinates.1, hrightCoordinates.1]
    exact him
  exact (natCode_mem_natCode_iff _ _).mp hcodes

theorem textbookERelation_isRelationOn :
    IsRelationOn TextbookEDomain.{u} TextbookERelation.{u} := by
  intro s hs
  rcases hs with
    ⟨i, k, m, n, hi, hk, hm, hn, hleft, hright, _him⟩
  intro j
  fin_cases j
  · apply mem_textbookEDomain_iff.mpr
    exact ⟨i, hi, k, hk, hleft⟩
  · apply mem_textbookEDomain_iff.mpr
    exact ⟨m, hm, n, hn, hright⟩

theorem textbookERelation_hasSetMinimaOn :
    HasSetMinimaOn TextbookEDomain.{u} TextbookERelation.{u} := by
  unfold TextbookEDomain
  apply (hasSetMinimaOn_iff_wellFounded_zfCarrier
    textbookEDomainZF.{u} TextbookERelation.{u}).mpr
  exact (WellFounded.onFun
    (f := fun x : ZFCarrier textbookEDomainZF.{u} =>
      (textbookENatCode x).1)
    (Nat.lt_wfRel).2).mono
    (fun _left _right h =>
      textbookENatCode_first_lt_of_relation h)

theorem textbookERelation_hasSetPredecessorsOn :
    HasSetPredecessorsOn TextbookEDomain.{u} TextbookERelation.{u} := by
  intro x hx
  rcases mem_textbookEDomain_iff.mp hx with ⟨m, hm, n, hn, rfl⟩
  exact ⟨ZFSet.prod m textbookEOmegaZF,
    textbookE_predecessorSet hm hn⟩

/-- The relation used for the textbook enumeration recursion is
well-founded and set-like on the actual set-coded domain. -/
theorem textbookERelation_isWellFoundedSetLikeOn :
    IsWellFoundedSetLikeOn TextbookEDomain.{u} TextbookERelation.{u} :=
  ⟨textbookERelation_isRelationOn,
    textbookERelation_hasSetMinimaOn,
    textbookERelation_hasSetPredecessorsOn⟩

namespace Model

/-! ## Closure and the internal set-likeness assertion -/

private theorem textbookE_orderedPair_components_mem
    {M left right : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : ZFSet.pair left right ∈ M) : left ∈ M ∧ right ∈ M := by
  have hsingletonPair : ({left} : ZFSet.{u}) ∈
      ZFSet.pair left right := by
    simp [ZFSet.pair]
  have hunorderedPair : ({left, right} : ZFSet.{u}) ∈
      ZFSet.pair left right := by
    simp [ZFSet.pair]
  have hsingletonM : ({left} : ZFSet.{u}) ∈ M :=
    hM.mem_trans hsingletonPair hpair
  have hunorderedM : ({left, right} : ZFSet.{u}) ∈ M :=
    hM.mem_trans hunorderedPair hpair
  constructor
  · exact hM.mem_trans (by simp) hsingletonM
  · exact hM.mem_trans (by simp) hunorderedM

theorem textbookERelation_predecessorsClosedIn
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    PredecessorsClosedIn (M : Set ZFSet.{u})
      TextbookEDomain TextbookERelation := by
  intro x hxM y hyDomain hyRelation
  rcases mem_textbookEDomain_iff.mp
    (textbookERelation_isRelationOn.right_mem hyRelation) with
    ⟨m, hm, n, hn, hx⟩
  subst x
  have hmM : m ∈ M :=
    (textbookE_orderedPair_components_mem hM.1 hxM).1
  have homegaM : textbookEOmegaZF ∈ M :=
    omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hproductM : ZFSet.prod m textbookEOmegaZF ∈ M :=
    prod_mem_of_isTransitiveZFModel hM hmM homegaM
  have hyProduct : y ∈ ZFSet.prod m textbookEOmegaZF :=
    (textbookE_predecessorSet hm hn y).mpr
      ⟨hyDomain, hyRelation⟩
  exact hM.1.mem_trans hyProduct hproductM

/-- The model internally verifies that the displayed relation is a relation
on the displayed domain and that every point has a predecessor set. -/
theorem satisfiesIn_textbookESetLikeRelationOnFormula
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula TextbookEFormula.domainFormula
      TextbookEFormula.relationFormula)
      (![] : Tuple ZFSet.{u} 0) := by
  rw [satisfiesIn_setLikeRelationOnFormula_iff]
  have hsingle (z : ZFSet.{u}) :
      snoc (![] : Tuple ZFSet.{u} 0) z = ![z] := by
    funext i
    fin_cases i
    rfl
  have hdouble (left right : ZFSet.{u}) :
      snoc (snoc (![] : Tuple ZFSet.{u} 0) left) right =
        ![left, right] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro left hleftM right hrightM hrelationFormula
    change left ∈ M at hleftM
    change right ∈ M at hrightM
    have hrelation : ClassRel TextbookERelation left right :=
      (satisfiesIn_textbookERelationFormula_iff
        hM hleftM hrightM).mp (by
          rw [← hdouble]
          exact hrelationFormula)
    have hleftDomain : left ∈ TextbookEDomain :=
      textbookERelation_isRelationOn.left_mem hrelation
    have hrightDomain : right ∈ TextbookEDomain :=
      textbookERelation_isRelationOn.right_mem hrelation
    constructor
    · rw [hsingle]
      apply (satisfiesIn_textbookEDomainFormula_iff hM hleftM).mpr
      exact hleftDomain
    · rw [hsingle]
      apply (satisfiesIn_textbookEDomainFormula_iff hM hrightM).mpr
      exact hrightDomain
  · intro x hxM hxFormula
    change x ∈ M at hxM
    have hxDomain : x ∈ TextbookEDomain :=
      (satisfiesIn_textbookEDomainFormula_iff hM hxM).mp (by
        rw [← hsingle]
        exact hxFormula)
    rcases mem_textbookEDomain_iff.mp hxDomain with
      ⟨m, hm, n, hn, hxPair⟩
    have hcomponentsM : m ∈ M ∧ n ∈ M := by
      apply textbookE_orderedPair_components_mem hM.1
      rw [← hxPair]
      exact hxM
    have homegaM : textbookEOmegaZF ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    have hpredecessorsM : ZFSet.prod m textbookEOmegaZF ∈ M :=
      prod_mem_of_isTransitiveZFModel hM hcomponentsM.1 homegaM
    refine ⟨ZFSet.prod m textbookEOmegaZF, hpredecessorsM, ?_⟩
    intro y hyM
    change y ∈ M at hyM
    rw [textbookE_predecessorSet hm hn y]
    constructor
    · rintro ⟨hyDomain, hyRelation⟩
      constructor
      · rw [hsingle]
        apply (satisfiesIn_textbookEDomainFormula_iff hM hyM).mpr
        exact hyDomain
      · rw [hdouble]
        apply (satisfiesIn_textbookERelationFormula_iff
          hM hyM hxM).mpr
        simpa only [hxPair] using hyRelation
    · rintro ⟨hyFormula, hyRelationFormula⟩
      constructor
      · apply (satisfiesIn_textbookEDomainFormula_iff hM hyM).mp
        rw [← hsingle]
        exact hyFormula
      · have hyRelation : ClassRel TextbookERelation y x :=
          (satisfiesIn_textbookERelationFormula_iff
            hM hyM hxM).mp (by
              rw [← hdouble]
              exact hyRelationFormula)
        simpa only [hxPair] using hyRelation

end Model

end

end Constructible
