/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteTupleAbsolute

/-!
# Absoluteness of finite function spaces

The formula for an unrestricted function space is not absolute to a
transitive model: the model may omit subsets of an infinite Cartesian
product.  This file therefore restricts the first input to a standard finite
ordinal.  The restriction is part of the graph formula, as required by
`Model.FunctionAbsoluteTo`; the formula is false away from its stated domain.

The guard says that the first input belongs to the internally least inductive
set.  In a transitive ZF model that set is the ambient von Neumann `omega`.
The function-space conjunct itself is exactly
`TextbookDefFormula.functionSpaceGraph`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

/-! ## Restricted-semantics helpers -/

private theorem satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_imp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s <->
      (SatisfiesIn M left s -> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

private theorem satisfiesIn_biimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn, satisfiesIn_imp_iff]
  tauto

private theorem satisfiesIn_boundedAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall x : ZFSet.{u}, x ∈ M -> x ∈ s set ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h x hxM hxSet
    by_contra hx
    exact h ⟨x, hxM, by simpa using hxSet, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxSet, hx⟩
    exact hx (h x hxM (by simpa using hxSet))

/-! ## A formula that denotes the standard omega -/

/-- `s i` is the internally least inductive set.  The inductiveness predicate
is the one whose exact semantics over arbitrary transitive ZF models was
proved in `TransitiveZFOmega`. -/
def standardOmegaAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (transitiveZFInductiveAt i)
    (FOFormula.all
      (FOFormula.imp
        (transitiveZFInductiveAt (Fin.last n))
        (FOFormula.boundedAll i.castSucc
          (.mem (Fin.last (n + 1)) (Fin.last n).castSucc))))

/-- In every transitive ZF model, `standardOmegaAt` denotes exactly the
ambient von Neumann `omega`. -/
theorem satisfiesIn_standardOmegaAt_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (standardOmegaAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  rw [standardOmegaAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff, satisfiesIn_imp_iff,
    satisfiesIn_boundedAll_iff, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinductiveFormula, hminimalFormula⟩
    have hinductive : ZFInductiveSetIn M (s i) :=
      (satisfiesIn_transitiveZFInductiveAt_iff hM.1
        (empty_mem_of_isTransitiveZFModel hM)
        (fun x hx => successor_mem_of_isTransitiveZFModel hM hx)
        i s hs).mp hinductiveFormula
    have hminimal : forall w : ZFSet.{u}, w ∈ M ->
        ZFInductiveSetIn M w -> s i ⊆ w := by
      intro w hwM hwInductive x hx
      have hwFormula :
          SatisfiesIn (M : Set ZFSet.{u})
            (transitiveZFInductiveAt (Fin.last n)) (snoc s w) := by
        apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1
          (empty_mem_of_isTransitiveZFModel hM)
          (fun z hz => successor_mem_of_isTransitiveZFModel hM hz)
          (Fin.last n) (snoc s w) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hwM
            · simpa using hs k)).mpr
        simpa only [snoc_last] using hwInductive
      exact hminimalFormula w hwM hwFormula x
        (hM.1.mem_trans hx (hs i)) hx
    let omegaM : ZFCarrier M := ⟨s i, hs i⟩
    exact zfCarrier_leastInductiveSet_eq_omega
      hM omegaM hinductive hminimal
  · intro homega
    have homegaM : Ordinal.omega0.toZFSet ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    have hnM : forall k : Nat, (k : Ordinal.{u}).toZFSet ∈ M :=
      natOrdinal_mem_of_isTransitiveZFModel hM
    constructor
    · apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1
        (empty_mem_of_isTransitiveZFModel hM)
        (fun x hx => successor_mem_of_isTransitiveZFModel hM hx)
        i s hs).mpr
      simpa only [homega] using omegaToZFSet_isInductiveSetIn M
    · intro w hwM hwFormula x hxM hxOmega
      have hwInductive : ZFInductiveSetIn M w := by
        simpa only [snoc_last] using
          (satisfiesIn_transitiveZFInductiveAt_iff hM.1
            (empty_mem_of_isTransitiveZFModel hM)
            (fun z hz => successor_mem_of_isTransitiveZFModel hM hz)
            (Fin.last n) (snoc s w) (by
              intro j
              refine Fin.lastCases ?_ (fun k => ?_) j
              · simpa using hwM
              · simpa using hs k)).mp hwFormula
      rw [homega] at hxOmega
      rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_ZFInductiveSetIn hwInductive hnM k

/-! ## The finite-domain guard -/

/-- Coordinate `domain` belongs to the internally defined standard omega. -/
def standardFiniteDomainAt {n : Nat} (domain : Fin n) : FOFormula n :=
  .ex (.conj
    (standardOmegaAt (Fin.last n))
    (.mem domain.castSucc (Fin.last n)))

/-- Exact restricted semantics of the finite-domain guard. -/
theorem satisfiesIn_standardFiniteDomainAt_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) {n : Nat}
    (domain : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (standardFiniteDomainAt domain) s <->
      exists k : Nat, s domain = natCode k := by
  simp only [standardFiniteDomainAt, SatisfiesIn,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨omega, homegaM, homegaFormula, hdomainOmega⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      by
        simpa only [snoc_last] using
          (satisfiesIn_standardOmegaAt_iff hM (Fin.last n)
            (snoc s omega) (by
              intro i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simpa using homegaM
              · simpa using hs j)).mp homegaFormula
    rw [homega] at hdomainOmega
    exact IndexedSequenceZF.mem_omega_iff_exists_natCode (s domain)
      |>.mp hdomainOmega
  · rintro ⟨k, hdomain⟩
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaM : omega ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    refine ⟨omega, homegaM, ?_, ?_⟩
    · apply (satisfiesIn_standardOmegaAt_iff hM
        (Fin.last n) (snoc s omega) (by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using homegaM
          · simpa using hs j)).mpr
      simp only [snoc_last, omega]
    · apply (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (s domain)).mpr
      exact ⟨k, hdomain⟩

/-! ## Guarded function-space graph -/

/-- The binary input domain for finite function spaces.  Layout is
`[domain, codomain]`, and `domain` must be a standard finite ordinal. -/
def FiniteFunctionSpaceTupleDomain :
    Set (Tuple ZFSet.{u} 2) :=
  {s | exists n : Nat, s 0 = natCode n}

/-- Layout `[domain, codomain, space]`.  The first conjunct makes the graph
false off `FiniteFunctionSpaceTupleDomain`; the second conjunct is the
unmodified general function-space formula. -/
def finiteFunctionSpaceGraph : FOFormula 3 :=
  .conj
    (standardFiniteDomainAt (0 : Fin 3))
    TextbookDefFormula.functionSpaceGraph

/-- On a standard finite domain, the unrestricted function-space formula has
the expected semantics inside every transitive ZF model. -/
theorem satisfiesIn_functionSpaceGraph_iff_of_standardFinite
    {M domain codomain space : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hdomain : domain ∈ M) (hcodomain : codomain ∈ M)
    (hspace : space ∈ M)
    (hfinite : exists n : Nat, domain = natCode n) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.functionSpaceGraph
        ![domain, codomain, space] <->
      space = ZFSet.funs domain codomain := by
  rcases hfinite with ⟨n, rfl⟩
  rw [TextbookDefFormula.functionSpaceGraph,
    TextbookDefFormula.functionSpaceAt, satisfiesIn_all_iff]
  simp only [satisfiesIn_biimp_iff, SatisfiesIn,
    TextbookDefFormula.isFunctionAt, snoc_last, snoc_castSucc]
  have hfunction (graph : ZFSet.{u}) (hgraphM : graph ∈ M) :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.isFunctionDeltaAt
            (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc).toFO
          (snoc ![natCode n, codomain, space] graph) <->
        ZFSet.IsFunc (natCode n) codomain graph := by
    have hassign :
        snoc ![natCode n, codomain, space] graph =
          ![natCode n, codomain, space, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    have hs : forall i,
        ![natCode n, codomain, space, graph] i ∈ M := by
      intro i
      fin_cases i
      · exact hdomain
      · exact hcodomain
      · exact hspace
      · exact hgraphM
    have habsolute := satisfiesIn_delta0_iff hM.1
      (TextbookDefFormula.isFunctionDeltaAt
        (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc)
      ![natCode n, codomain, space, graph] hs
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_isFunctionDeltaAt] at habsolute
    have hdomainValue :
        ![natCode n, codomain, space, graph] ((0 : Fin 3).castSucc) =
          natCode n := rfl
    have hcodomainValue :
        ![natCode n, codomain, space, graph] ((1 : Fin 3).castSucc) =
          codomain := rfl
    have hgraphValue :
        ![natCode n, codomain, space, graph] (Fin.last 3) = graph := rfl
    rw [hdomainValue, hcodomainValue, hgraphValue] at habsolute
    exact habsolute
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    constructor
    · intro hgraphSpace
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspace
      exact (hfunction graph hgraphM).mp
        ((h graph hgraphM).mp hgraphSpace)
    · intro hgraphFunc
      have hgraphM : graph ∈ M :=
        finiteIsFunc_mem_of_isTransitiveZFModel
          hM hcodomain hgraphFunc
      exact (h graph hgraphM).mpr
        ((hfunction graph hgraphM).mpr hgraphFunc)
  · intro hspaceEq graph hgraphM
    constructor
    · intro hgraphSpace
      apply (hfunction graph hgraphM).mpr
      apply ZFSet.mem_funs.mp
      rwa [← hspaceEq]
    · intro hgraphFormula
      change graph ∈ space
      rw [hspaceEq, ZFSet.mem_funs]
      exact (hfunction graph hgraphM).mp hgraphFormula

/-- Exact restricted semantics of the guarded graph. -/
theorem satisfiesIn_finiteFunctionSpaceGraph_iff
    {M domain codomain space : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hdomain : domain ∈ M) (hcodomain : codomain ∈ M)
    (hspace : space ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) finiteFunctionSpaceGraph
        ![domain, codomain, space] <->
      (exists n : Nat, domain = natCode n) ∧
        space = ZFSet.funs domain codomain := by
  rw [finiteFunctionSpaceGraph]
  simp only [SatisfiesIn]
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (0 : Fin 3) ![domain, codomain, space] (by
      intro i
      fin_cases i
      · exact hdomain
      · exact hcodomain
      · exact hspace)]
  constructor
  · rintro ⟨hfinite, hspaceFormula⟩
    exact ⟨hfinite,
      (satisfiesIn_functionSpaceGraph_iff_of_standardFinite
        hM hdomain hcodomain hspace hfinite).mp hspaceFormula⟩
  · rintro ⟨hfinite, hspaceEq⟩
    exact ⟨hfinite,
      (satisfiesIn_functionSpaceGraph_iff_of_standardFinite
        hM hdomain hcodomain hspace hfinite).mpr hspaceEq⟩

/-- Finite function-space formation, with binary input layout
`[domain, codomain]`, is a standard absolute function. -/
theorem finiteFunctionSpace_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u})
      FiniteFunctionSpaceTupleDomain
      (fun s : Tuple ZFSet.{u} 2 => ZFSet.funs (s 0) (s 1))
      finiteFunctionSpaceGraph := by
  constructor
  · intro s hsM hsDomain
    rcases hsDomain with ⟨n, hdomain⟩
    change ZFSet.funs (s 0) (s 1) ∈ M
    rw [hdomain]
    exact textbookTupleSpace_mem_of_isTransitiveZFModel hM (hsM 1) n
  · intro s space hsM hspaceM
    have hassign : snoc s space = ![s 0, s 1, space] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact satisfiesIn_finiteFunctionSpaceGraph_iff
      hM (hsM 0) (hsM 1) hspaceM

end

end Model

end Constructible
