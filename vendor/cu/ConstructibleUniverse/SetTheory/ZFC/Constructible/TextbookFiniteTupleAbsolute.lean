/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDefinability
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFOmega
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFReplacement

/-!
# Finite tuple spaces inside transitive ZF models

The bounded predicate `IsFunc(n,a,f)` is absolute to a transitive model, but
that observation alone does not identify the model's function space with the
ambient `a^n`: one must also prove that every ambient function graph with
finite domain belongs to the model.  This file supplies that missing closure
argument before constructing the whole finite function space internally.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Every finite function graph is a tuple graph -/

theorem exists_textbookTupleGraph_eq_of_isFunc
    {a f : ZFSet.{u}} {n : Nat}
    (hf : ZFSet.IsFunc (natCode n) a f) :
    ∃ s : Tuple (ZFCarrier a) n, textbookTupleGraph s = f := by
  classical
  have hindex : ∀ i : Fin n, (natCode i.1 : ZFSet.{u}) ∈ natCode n := by
    intro i
    exact (mem_natCode_iff_exists_fin _ _).mpr ⟨i, rfl⟩
  choose value hpair hunique using fun i : Fin n => hf.2 (natCode i.1) (hindex i)
  have hvalue : ∀ i : Fin n, value i ∈ a := by
    intro i
    exact (ZFSet.pair_mem_prod.mp (hf.1 (hpair i))).2
  let s : Tuple (ZFCarrier a) n := fun i => ⟨value i, hvalue i⟩
  refine ⟨s, ?_⟩
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, hi⟩
    rw [← hi]
    exact hpair i
  · intro hq
    rcases ZFSet.mem_prod.mp (hf.1 hq) with
      ⟨index, hindexMem, output, _houtput, hqPair⟩
    rcases (mem_natCode_iff_exists_fin index n).mp hindexMem with ⟨i, rfl⟩
    have houtputValue : output = value i := hunique i output (by
      change ZFSet.pair (natCode i.1) output ∈ f
      rw [← hqPair]
      exact hq)
    apply (mem_textbookTupleGraph_iff s).mpr
    refine ⟨i, ?_⟩
    change ZFSet.pair (natCode i.1) (value i) = q
    rw [← houtputValue, ← hqPair]

namespace Model

noncomputable section

/-- A transitive ZF model is closed under adjoining one member to a set. -/
theorem textbookInsert_mem_of_isTransitiveZFModel
    {M x a : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hx : x ∈ M) (ha : a ∈ M) : insert x a ∈ M := by
  have hsingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hpair : ({{x}, a} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hsingleton ha
  have hunion := sUnion_mem_of_isTransitiveZFModel hM hpair
  change ZFSet.sUnion ({{x}, a} : ZFSet.{u}) ∈ M at hunion
  rw [ZFSet.sUnion_pair] at hunion
  rw [ZFSet.insert_eq]
  exact hunion

/-- The canonical graph of a finite tuple of members of `a` belongs to `M`. -/
theorem textbookTupleGraph_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    {n : Nat} (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ M := by
  induction n with
  | zero =>
      have hempty : textbookTupleGraph s = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro q hq
        rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, _⟩
        exact Fin.elim0 i
      rw [hempty]
      exact empty_mem_of_isTransitiveZFModel hM
  | succ n ih =>
      let initial : Tuple (ZFCarrier a) n := fun i => s i.castSucc
      let finalEntry : ZFCarrier a := s (Fin.last n)
      have hs : s = snoc initial finalEntry := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [finalEntry]
        · simp [initial]
      rw [hs, textbookTupleGraph_snoc]
      apply textbookInsert_mem_of_isTransitiveZFModel hM
      · apply kuratowskiPair_mem_of_isTransitiveZFModel hM
        · exact natOrdinal_mem_of_isTransitiveZFModel hM n
        · exact hM.1.mem_trans finalEntry.2 ha
      · exact ih initial

/-- Every ambient function graph from a standard finite ordinal into `a`
belongs to a transitive ZF model containing `a`. -/
theorem finiteIsFunc_mem_of_isTransitiveZFModel
    {M a f : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    {n : Nat} (hf : ZFSet.IsFunc (natCode n) a f) : f ∈ M := by
  rcases exists_textbookTupleGraph_eq_of_isFunc hf with ⟨s, rfl⟩
  exact textbookTupleGraph_mem_of_isTransitiveZFModel hM ha s

/-! ## A reusable Delta-zero absoluteness bridge -/

/-- Raw restricted satisfaction of a bounded formula agrees with its ambient
semantics when all parameters belong to a transitive carrier. -/
theorem satisfiesIn_delta0_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (phi : Delta0Formula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) phi.toFO s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem phi.toFO s := by
  let sM : Tuple (ZFCarrier M) n := fun i => ⟨s i, hs i⟩
  have hval : (fun i => (sM i).1) = s := by
    funext i
    rfl
  have hdeltaVal : Delta0Formula.val sM = s := by
    funext i
    rfl
  calc
    SatisfiesIn (M : Set ZFSet.{u}) phi.toFO s ↔
        FOFormula.Satisfies (zfCarrierMem M) phi.toFO sM := by
      have hbridge :=
        (Model.satisfies_subtype_iff_satisfiesIn
          (M : Set ZFSet.{u}) phi.toFO sM).symm
      rw [hval] at hbridge
      exact hbridge
    _ ↔ FOFormula.Satisfies Delta0Formula.ZFMem phi.toFO s := by
      have habsolute :=
        Delta0Formula.satisfies_toFO_absolute hM phi sM
      rw [hdeltaVal] at habsolute
      exact habsolute

/-! ## Internal power-set witnesses -/

/-- The Power Set axiom inside `M`, stated without identifying its witness
with the ambient powerset.  It contains exactly the subsets of `x` that are
themselves members of `M`. -/
theorem exists_internalPowerSet
    {M x : ZFSet.{u}} (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ∃ power : ZFCarrier M,
      ∀ y : ZFCarrier M, y.1 ∈ power.1 ↔ y.1 ⊆ x := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .powerSet xM with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  intro y
  have hpowerY := hpower y
  change y.1 ∈ power.1 ↔
    ∀ z : ZFCarrier M, z.1 ∈ y.1 → z.1 ∈ x at hpowerY
  constructor
  · intro hyPower z hzy
    have hzM : z ∈ M := hM.1.mem_trans hzy y.2
    exact (hpowerY.mp hyPower) ⟨z, hzM⟩ hzy
  · intro hySubset
    apply hpowerY.mpr
    intro z hzy
    exact hySubset hzy

end

end Model

namespace TextbookDefFormula

/-! ## A bounded formula for Cartesian-product membership -/

/-- `candidate` is a Kuratowski pair with first coordinate in `left` and
second coordinate in `right`. -/
def productMemberDeltaAt {n : Nat}
    (candidate left right : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx left
    (Delta0Formula.boundedEx right.castSucc
      (Delta0Formula.kuratowskiPairEqAt
        candidate.castSucc.castSucc
        (Fin.last n).castSucc
        (Fin.last (n + 1))))

@[simp]
theorem satisfies_productMemberDeltaAt {n : Nat}
    (candidate left right : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (productMemberDeltaAt candidate left right) s ↔
      s candidate ∈ ZFSet.prod (s left) (s right) := by
  simp only [productMemberDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, ZFSet.mem_prod]

/-- Layout `[left, right, candidate]`. -/
def productMemberDelta : Delta0Formula 3 :=
  productMemberDeltaAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

def productMemberFormula : FOFormula 3 :=
  productMemberDelta.toFO

@[simp]
theorem satisfies_productMemberFormula
    (left right candidate : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem productMemberFormula
        ![left, right, candidate] ↔
      candidate ∈ ZFSet.prod left right := by
  simp [productMemberFormula, productMemberDelta]

/-- Layout `[domain, codomain, graph]`. -/
def isFunctionDelta : Delta0Formula 3 :=
  isFunctionDeltaAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

def isFunctionFormula : FOFormula 3 :=
  isFunctionDelta.toFO

@[simp]
theorem satisfies_isFunctionFormula
    (domain codomain graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem isFunctionFormula
        ![domain, codomain, graph] ↔
      ZFSet.IsFunc domain codomain graph := by
  simp [isFunctionFormula, isFunctionDelta]

end TextbookDefFormula

namespace Model

noncomputable section

/-! ## Cartesian products in transitive ZF models -/

/-- Binary union closure, derived from Pairing and Union inside the model. -/
theorem textbookUnion_mem_of_isTransitiveZFModel
    {M x y : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hx : x ∈ M) (hy : y ∈ M) : x ∪ y ∈ M := by
  have hpair : ({x, y} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hx hy
  simpa only [ZFSet.sUnion_pair] using
    sUnion_mem_of_isTransitiveZFModel hM hpair

theorem satisfiesIn_productMemberFormula_iff
    {M left right candidate : ZFSet.{u}}
    (hM : M.IsTransitive) (hleft : left ∈ M)
    (hright : right ∈ M) (hcandidate : candidate ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.productMemberFormula
        ![left, right, candidate] ↔
      candidate ∈ ZFSet.prod left right := by
  have hs : ∀ i : Fin 3, ![left, right, candidate] i ∈ M := by
    intro i
    fin_cases i
    · exact hleft
    · exact hright
    · exact hcandidate
  rw [TextbookDefFormula.productMemberFormula,
    satisfiesIn_delta0_iff hM TextbookDefFormula.productMemberDelta
      ![left, right, candidate] hs]
  simpa only [TextbookDefFormula.productMemberFormula] using
    (TextbookDefFormula.satisfies_productMemberFormula
      left right candidate)

/-- A transitive ZF model is closed under the ambient Cartesian product.
The proof uses two internal power-set witnesses only as a bounding set for
Separation; it never asserts that either witness is an ambient powerset. -/
theorem prod_mem_of_isTransitiveZFModel
    {M left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M) :
    ZFSet.prod left right ∈ M := by
  let union : ZFSet.{u} := left ∪ right
  have hunion : union ∈ M :=
    textbookUnion_mem_of_isTransitiveZFModel hM hleft hright
  rcases exists_internalPowerSet hM hunion with ⟨powerOne, hpowerOne⟩
  rcases exists_internalPowerSet hM powerOne.2 with
    ⟨powerTwo, hpowerTwo⟩
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨left, hleft⟩, ⟨right, hright⟩]
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.productMemberFormula params powerTwo
  have hassign : ∀ q : ZFSet.{u},
      snoc (zfCarrierTupleVal params) q = ![left, right, q] := by
    intro q
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (powerTwo.1.sep fun q =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.productMemberFormula
          (snoc (zfCarrierTupleVal params) q)) =
        ZFSet.prod left right := by
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hqPowerTwo, hqFormula⟩
      have hqM : q ∈ M :=
        hM.1.mem_trans hqPowerTwo powerTwo.2
      apply (satisfiesIn_productMemberFormula_iff
        hM.1 hleft hright hqM).mp
      rwa [← hassign q]
    · intro hqProd
      rcases ZFSet.mem_prod.mp hqProd with
        ⟨x, hxLeft, y, hyRight, hqPair⟩
      have hxM : x ∈ M := hM.1.mem_trans hxLeft hleft
      have hyM : y ∈ M := hM.1.mem_trans hyRight hright
      have hqM : q ∈ M := by
        rw [hqPair]
        exact kuratowskiPair_mem_of_isTransitiveZFModel hM hxM hyM
      have hsingletonM : ({x} : ZFSet.{u}) ∈ M :=
        singleton_mem_of_isTransitiveZFModel hM hxM
      have hunorderedM : ({x, y} : ZFSet.{u}) ∈ M :=
        unorderedPair_mem_of_isTransitiveZFModel hM hxM hyM
      have hsingletonSubset : ({x} : ZFSet.{u}) ⊆ union := by
        intro z hz
        have hzx : z = x := by simpa using hz
        subst z
        exact ZFSet.mem_union.mpr (Or.inl hxLeft)
      have hunorderedSubset : ({x, y} : ZFSet.{u}) ⊆ union := by
        intro z hz
        rcases ZFSet.mem_pair.mp hz with rfl | rfl
        · exact ZFSet.mem_union.mpr (Or.inl hxLeft)
        · exact ZFSet.mem_union.mpr (Or.inr hyRight)
      have hsingletonPowerOne : ({x} : ZFSet.{u}) ∈ powerOne.1 :=
        (hpowerOne ⟨{x}, hsingletonM⟩).mpr hsingletonSubset
      have hunorderedPowerOne : ({x, y} : ZFSet.{u}) ∈ powerOne.1 :=
        (hpowerOne ⟨{x, y}, hunorderedM⟩).mpr hunorderedSubset
      have hqSubsetPowerOne : q ⊆ powerOne.1 := by
        intro z hz
        rw [hqPair, ZFSet.pair] at hz
        rcases ZFSet.mem_pair.mp hz with hzx | hzu
        · simpa only [hzx] using hsingletonPowerOne
        · simpa only [hzu] using hunorderedPowerOne
      have hqPowerTwo : q ∈ powerTwo.1 :=
        (hpowerTwo ⟨q, hqM⟩).mpr hqSubsetPowerOne
      refine ⟨hqPowerTwo, ?_⟩
      rw [hassign q]
      exact (satisfiesIn_productMemberFormula_iff
        hM.1 hleft hright hqM).mpr hqProd
  rw [hsepEq] at hsep
  exact hsep

/-! ## Finite function spaces in transitive ZF models -/

theorem satisfiesIn_isFunctionFormula_iff
    {M domain codomain graph : ZFSet.{u}}
    (hM : M.IsTransitive) (hdomain : domain ∈ M)
    (hcodomain : codomain ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.isFunctionFormula
        ![domain, codomain, graph] ↔
      ZFSet.IsFunc domain codomain graph := by
  have hs : ∀ i : Fin 3, ![domain, codomain, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact hdomain
    · exact hcodomain
    · exact hgraph
  rw [TextbookDefFormula.isFunctionFormula,
    satisfiesIn_delta0_iff hM TextbookDefFormula.isFunctionDelta
      ![domain, codomain, graph] hs]
  simpa only [TextbookDefFormula.isFunctionFormula] using
    (TextbookDefFormula.satisfies_isFunctionFormula
      domain codomain graph)

/-- The full ambient finite function space `a^n` belongs to every transitive
ZF model containing `a`.  The reverse inclusion in the final Separation
identity is precisely where finite-graph closure is used. -/
theorem textbookTupleSpace_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n : Nat) : textbookTupleSpace a n ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hprodM : ZFSet.prod (natCode n) a ∈ M :=
    prod_mem_of_isTransitiveZFModel hM hnM ha
  rcases exists_internalPowerSet hM hprodM with ⟨power, hpower⟩
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨natCode n, hnM⟩, ⟨a, ha⟩]
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.isFunctionFormula params power
  have hassign : ∀ graph : ZFSet.{u},
      snoc (zfCarrierTupleVal params) graph = ![natCode n, a, graph] := by
    intro graph
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (power.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.isFunctionFormula
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookTupleSpace a n := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookTupleSpace_iff]
    constructor
    · rintro ⟨hgraphPower, hgraphFormula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphPower power.2
      apply (satisfiesIn_isFunctionFormula_iff
        hM.1 hnM ha hgraphM).mp
      rwa [← hassign graph]
    · intro hgraphFunc
      have hgraphM : graph ∈ M :=
        finiteIsFunc_mem_of_isTransitiveZFModel hM ha hgraphFunc
      have hgraphPower : graph ∈ power.1 :=
        (hpower ⟨graph, hgraphM⟩).mpr hgraphFunc.1
      refine ⟨hgraphPower, ?_⟩
      rw [hassign graph]
      exact (satisfiesIn_isFunctionFormula_iff
        hM.1 hnM ha hgraphM).mpr hgraphFunc
  rw [hsepEq] at hsep
  exact hsep

end

end Model

end Constructible
