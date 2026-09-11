/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalArithmeticLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepLCarrier

/-!
# Operation semantics for the textbook E step over L

This file proves exact `LCarrier` semantics for the set operations occurring
in the five clauses of the textbook recursion for `E`.  Unbounded quantifiers
are handled over the proper-class carrier itself.  The reverse directions use
explicit constructibility closure theorems for the operation values and for
the finite witnesses selected by the formulas.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_kuratowskiPairEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt output left right).toFO s <->
      (s output).1 = ZFSet.pair (s left).1 (s right).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt output left right) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt])

@[simp]
theorem satisfies_successorAt_lCarrier {n : Nat}
    (output input : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.successorAt output input).toFO s <->
      (s output).1 = insert (s input).1 (s input).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.successorAt output input) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt])

/-! ## Coordinate embeddings -/

@[simp]
theorem satisfies_formula3At_lCarrier
    (formula : FOFormula 3) {n : Nat} (x y z : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula3At formula x y z) s <->
      FOFormula.Satisfies LMem formula ![s x, s y, s z] := by
  rw [TextbookEFormula.formula3At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![x, y, z] i)) =
      ![s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula4At_lCarrier
    (formula : FOFormula 4) {n : Nat} (v w x y : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula4At formula v w x y) s <->
      FOFormula.Satisfies LMem formula ![s v, s w, s x, s y] := by
  rw [TextbookEFormula.formula4At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y] i)) =
      ![s v, s w, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula5At_lCarrier
    (formula : FOFormula 5) {n : Nat} (v w x y z : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula5At formula v w x y z) s <->
      FOFormula.Satisfies LMem formula ![s v, s w, s x, s y, s z] := by
  rw [TextbookEFormula.formula5At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y, z] i)) =
      ![s v, s w, s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

/-! ## Boolean set operations -/

@[simp]
theorem satisfies_relativeDifferenceOutputFormula_lCarrier
    (space removed output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] <->
      output.1 = relativeDifferenceZF space.1 removed.1 := by
  rw [TextbookDefFormula.relativeDifferenceOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    TextbookDefFormula.satisfies_relativeDifferenceMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [mem_relativeDifferenceZF_iff]
    constructor
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx output.2⟩
      exact (h xL).mp hx
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx.1 space.2⟩
      exact (h xL).mpr hx
  · intro houtput x
    change x.1 ∈ output.1 <-> x.1 ∈ space.1 ∧ x.1 ∉ removed.1
    rw [houtput, mem_relativeDifferenceZF_iff]

@[simp]
theorem satisfies_intersectionOutputFormula_lCarrier
    (left right output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] <->
      output.1 = intersectionZF left.1 right.1 := by
  rw [TextbookDefFormula.intersectionOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    TextbookDefFormula.satisfies_intersectionMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [mem_intersectionZF_iff]
    constructor
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx output.2⟩
      exact (h xL).mp hx
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx.1 left.2⟩
      exact (h xL).mpr hx
  · intro houtput x
    change x.1 ∈ output.1 <-> x.1 ∈ left.1 ∧ x.1 ∈ right.1
    rw [houtput, mem_intersectionZF_iff]

/-! ## Total graph lookup -/

/-- Every displayed value of a constructible graph is constructible. -/
theorem graphValue_mem_L
    {graph key value : ZFSet.{u}} (hgraph : graph ∈ L)
    (hvalue : ZFSet.pair key value ∈ graph) : value ∈ L := by
  have hpairL : ZFSet.pair key value ∈ L :=
    mem_L_of_mem hvalue hgraph
  have hunorderedPair : ({key, value} : ZFSet.{u}) ∈
      ZFSet.pair key value := by
    simp [ZFSet.pair]
  have hunorderedPairL : ({key, value} : ZFSet.{u}) ∈ L :=
    mem_L_of_mem hunorderedPair hpairL
  exact mem_L_of_mem (by simp) hunorderedPairL

@[simp]
theorem satisfies_graphValueAt_lCarrier {n : Nat}
    (graph key value : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.graphValueAt graph key value) s <->
      ZFSet.pair (s key).1 (s value).1 ∈ (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.graphValueDeltaAt graph key value) s).trans
    (TextbookDefFormula.satisfies_graphValueAt graph key value
      (fun i => (s i).1))

@[simp]
theorem satisfies_emptyDeltaAt_lCarrier {n : Nat}
    (index : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.emptyDeltaAt index).toFO s <->
      (s index).1 = (∅ : ZFSet.{u}) := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.emptyDeltaAt index) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_emptyDeltaAt])

@[simp]
theorem satisfies_uniqueGraphValueAt_lCarrier {n : Nat}
    (graph key output : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.uniqueGraphValueAt graph key output) s <->
      IsUniqueGraphValue (s graph).1 (s key).1 (s output).1 := by
  rw [TextbookDefFormula.uniqueGraphValueAt]
  simp only [FOFormula.Satisfies, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphValueAt_lCarrier,
    snoc_last, snoc_castSucc, IsUniqueGraphValue]
  constructor
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hother
    let otherL : LCarrier.{u} :=
      ⟨other, graphValue_mem_L (s graph).2 hother⟩
    exact congrArg Subtype.val (hunique otherL hother)
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hother
    apply Subtype.ext
    exact hunique other.1 hother

@[simp]
theorem satisfies_hasUniqueGraphValueAt_lCarrier {n : Nat}
    (graph key : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.hasUniqueGraphValueAt graph key) s <->
      ∃ value : ZFSet.{u},
        IsUniqueGraphValue (s graph).1 (s key).1 value := by
  rw [TextbookDefFormula.hasUniqueGraphValueAt]
  simp only [FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt_lCarrier, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨value, hvalue⟩
    exact ⟨value.1, hvalue⟩
  · rintro ⟨value, hvalue⟩
    let valueL : LCarrier.{u} :=
      ⟨value, graphValue_mem_L (s graph).2 hvalue.1⟩
    exact ⟨valueL, hvalue⟩

@[simp]
theorem satisfies_uniqueGraphLookupFormula_lCarrier_iff
    (graph key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.uniqueGraphLookupFormula
        ![graph, key, output] <->
      output.1 = uniqueGraphLookupZF graph.1 key.1 := by
  rw [TextbookDefFormula.uniqueGraphLookupFormula]
  simp only [FOFormula.satisfies_disj, FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt_lCarrier,
    satisfies_hasUniqueGraphValueAt_lCarrier,
    satisfies_emptyDeltaAt_lCarrier]
  change
    (IsUniqueGraphValue graph.1 key.1 output.1 ∨
      ((¬ ∃ value : ZFSet.{u},
          IsUniqueGraphValue graph.1 key.1 value) ∧
        output.1 = (∅ : ZFSet.{u}))) <->
      output.1 = uniqueGraphLookupZF graph.1 key.1
  constructor
  · rintro (houtput | ⟨hnot, hempty⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        houtput.1 houtput.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u},
            ZFSet.pair key.1 value ∈ graph.1 := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hempty,
        uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro houtput
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key.1 value ∈ graph.1
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookup := uniqueGraphLookupZF_eq_of_unique hvalue hunique
      rw [houtput, hlookup]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← existsUnique_graphValue_iff] using hunique
      · rw [houtput,
          uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

/-! ## Finite function spaces -/

@[simp]
theorem satisfies_standardFiniteDomainAt_lCarrier {n : Nat}
    (domain : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (standardFiniteDomainAt domain) s <->
      ∃ k : Nat, (s domain).1 = natCode k := by
  rw [standardFiniteDomainAt, FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homegaFormula, hdomainOmega⟩
    have homega : omega = omegaLCarrier := by
      simpa only [snoc_last] using
        (satisfies_standardOmegaAt_lCarrier
          (Fin.last n) (snoc s omega)).mp homegaFormula
    subst omega
    have hdomainOmega' : (s domain).1 ∈ omegaLCarrier.1 := by
      change (snoc s omegaLCarrier domain.castSucc).1 ∈
        (snoc s omegaLCarrier (Fin.last n)).1 at hdomainOmega
      simpa only [snoc_castSucc, snoc_last] using hdomainOmega
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (s domain).1).mp hdomainOmega'
  · rintro ⟨k, hdomain⟩
    refine ⟨omegaLCarrier, ?_, ?_⟩
    · apply (satisfies_standardOmegaAt_lCarrier
        (Fin.last n) (snoc s omegaLCarrier)).mpr
      simp only [snoc_last]
    · change (snoc s omegaLCarrier domain.castSucc).1 ∈
        (snoc s omegaLCarrier (Fin.last n)).1
      simp only [snoc_castSucc, snoc_last]
      rw [hdomain]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode k)).mpr ⟨k, rfl⟩

@[simp]
theorem satisfies_isFunctionAt_lCarrier {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.isFunctionAt graph domain codomain) s <->
      ZFSet.IsFunc (s domain).1 (s codomain).1 (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.isFunctionDeltaAt graph domain codomain) s).trans
    (TextbookDefFormula.satisfies_isFunctionAt graph domain codomain
      (fun i => (s i).1))

@[simp]
theorem satisfies_functionSpaceGraph_lCarrier_natCode_iff
    (n : Nat) (codomain space : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.functionSpaceGraph
        ![TextbookNatFormula.textbookNatCodeLCarrier n,
          codomain, space] <->
      space.1 = ZFSet.funs (natCode n) codomain.1 := by
  rw [TextbookDefFormula.functionSpaceGraph,
    TextbookDefFormula.functionSpaceAt, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_isFunctionAt_lCarrier, snoc_last, snoc_castSucc]
  change
    (∀ graph : LCarrier.{u},
      graph.1 ∈ space.1 <->
        ZFSet.IsFunc (natCode n) codomain.1 graph.1) <-> _
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    constructor
    · intro hgraphSpace
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphSpace space.2⟩
      exact (h graphL).mp hgraphSpace
    · intro hfunc
      have hgraphTupleSpace : graph ∈ textbookTupleSpace codomain.1 n :=
        mem_textbookTupleSpace_iff.mpr hfunc
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphTupleSpace
          (textbookTupleSpace_mem_L codomain.2 n)⟩
      exact (h graphL).mpr hfunc
  · intro hspace graph
    rw [hspace, ZFSet.mem_funs]

@[simp]
theorem satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
    (n : Nat) (codomain space : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteFunctionSpaceGraph
        ![TextbookNatFormula.textbookNatCodeLCarrier n,
          codomain, space] <->
      space.1 = ZFSet.funs (natCode n) codomain.1 := by
  rw [finiteFunctionSpaceGraph, FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hspace⟩
    exact (satisfies_functionSpaceGraph_lCarrier_natCode_iff
      n codomain space).mp hspace
  · intro hspace
    refine ⟨?_,
      (satisfies_functionSpaceGraph_lCarrier_natCode_iff
        n codomain space).mpr hspace⟩
    exact (satisfies_standardFiniteDomainAt_lCarrier
      (0 : Fin 3)
      ![TextbookNatFormula.textbookNatCodeLCarrier n,
        codomain, space]).mpr ⟨n, rfl⟩

/-! ## Existential projection -/

@[simp]
theorem satisfies_existsProjMemberDeltaAt_lCarrier {n : Nat}
    (a arity relation graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.existsProjMemberDeltaAt
          a arity relation graph).toFO s <->
      (∃ index : ZFSet.{u}, index ∈ (s arity).1) ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ value : ZFSet.{u}, value ∈ (s a).1 ∧
            insert (ZFSet.pair (s arity).1 value) (s graph).1 ∈
              (s relation).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.existsProjMemberDeltaAt
        a arity relation graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_existsProjMemberDeltaAt])

@[simp]
theorem satisfies_existsProjOutputMemberCondition_lCarrier_natCode_iff
    (n : Nat) (a relation output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph] <->
      graph.1 ∈ textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
  rw [TextbookDefFormula.existsProjOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    apply mem_textbookExistsProjCodeZF_iff.mpr
    refine ⟨⟨n, rfl⟩, ?_⟩
    exact (satisfies_existsProjMemberDeltaAt_lCarrier
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
      ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
        relation, output, graph]).mp hmember
  · intro hgraph
    have hcomponents := mem_textbookExistsProjCodeZF_iff.mp hgraph
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_existsProjMemberDeltaAt_lCarrier
        (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_existsProjOutputFormula_lCarrier_natCode_iff
    (n : Nat) (a relation output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output] <->
      output.1 =
        textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
  rw [TextbookDefFormula.existsProjOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            relation, output] graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.existsProjOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              relation, output] graph) <->
        graph.1 ∈
          textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              relation, output] graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            relation, output, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_existsProjOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL :
      textbookExistsProjCodeZF a.1 (natCode n) relation.1 ∈ L := by
    rw [textbookExistsProjCodeZF_natCode]
    exact textbookExistsProjZF_mem_L a.2 relation.2 n
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

/-! ## Atomic membership and equality relations -/

@[simp]
theorem satisfies_dInMemberDeltaAt_lCarrier {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.dInMemberDeltaAt
          a arity left right graph).toFO s <->
      (s left).1 ∈ (s arity).1 ∧ (s right).1 ∈ (s arity).1 ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ x : ZFSet.{u}, x ∈ (s a).1 ∧
            ∃ y : ZFSet.{u}, y ∈ (s a).1 ∧
              ZFSet.pair (s left).1 x ∈ (s graph).1 ∧
              ZFSet.pair (s right).1 y ∈ (s graph).1 ∧ x ∈ y := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.dInMemberDeltaAt
        a arity left right graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_dInMemberDeltaAt])

@[simp]
theorem satisfies_dEqMemberDeltaAt_lCarrier {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.dEqMemberDeltaAt
          a arity left right graph).toFO s <->
      (s left).1 ∈ (s arity).1 ∧ (s right).1 ∈ (s arity).1 ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ x : ZFSet.{u}, x ∈ (s a).1 ∧
            ZFSet.pair (s left).1 x ∈ (s graph).1 ∧
              ZFSet.pair (s right).1 x ∈ (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.dEqMemberDeltaAt
        a arity left right graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_dEqMemberDeltaAt])

@[simp]
theorem satisfies_dInOutputMemberCondition_lCarrier_natCode_iff
    (n i j : Nat) (a output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.dInOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph] <->
      graph.1 ∈ textbookDInZF a.1 n i j := by
  rw [TextbookDefFormula.dInOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph.1 ∈ textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      apply mem_textbookDInCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfies_dInMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mp hmember
    simpa only [textbookDInCodeZF_natCode] using hcode
  · intro hgraph
    have hcode : graph.1 ∈ textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      simpa only [textbookDInCodeZF_natCode] using hgraph
    have hcomponents := mem_textbookDInCodeZF_iff.mp hcode
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 6)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_dInMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_dEqOutputMemberCondition_lCarrier_natCode_iff
    (n i j : Nat) (a output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph] <->
      graph.1 ∈ textbookDEqZF a.1 n i j := by
  rw [TextbookDefFormula.dEqOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph.1 ∈ textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      apply mem_textbookDEqCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfies_dEqMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mp hmember
    simpa only [textbookDEqCodeZF_natCode] using hcode
  · intro hgraph
    have hcode : graph.1 ∈ textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      simpa only [textbookDEqCodeZF_natCode] using hgraph
    have hcomponents := mem_textbookDEqCodeZF_iff.mp hcode
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 6)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_dEqMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_dInOutputFormula_lCarrier_natCode_iff
    (n i j : Nat) (a output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.dInOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, output] <->
      output.1 = textbookDInZF a.1 n i j := by
  rw [TextbookDefFormula.dInOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.dInOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output]
          graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.dInOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph) <->
        graph.1 ∈ textbookDInZF a.1 n i j := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output, graph] := by
      funext k
      fin_cases k <;> rfl
    rw [hassign,
      satisfies_dInOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL : textbookDInZF a.1 n i j ∈ L :=
    textbookDInZF_mem_L a.2 n i j
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

@[simp]
theorem satisfies_dEqOutputFormula_lCarrier_natCode_iff
    (n i j : Nat) (a output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.dEqOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, output] <->
      output.1 = textbookDEqZF a.1 n i j := by
  rw [TextbookDefFormula.dEqOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.dEqOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output]
          graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.dEqOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph) <->
        graph.1 ∈ textbookDEqZF a.1 n i j := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output, graph] := by
      funext k
      fin_cases k <;> rfl
    rw [hassign,
      satisfies_dEqOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL : textbookDEqZF a.1 n i j ∈ L :=
    textbookDEqZF_mem_L a.2 n i j
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

/-! ## Constructor-code guards -/

@[simp]
theorem satisfies_natLiteralDeltaAt_lCarrier
    (k : Nat) {n : Nat} (index : Fin n)
    (s : Tuple LCarrier.{u} n) :
    Delta0Formula.Satisfies LMem
        (Delta0Formula.natLiteralDeltaAt k index) s <->
      (s index).1 = (natCode k : ZFSet.{u}) := by
  exact
    (Delta0Formula.satisfies_lCarrier_absolute
      (Delta0Formula.natLiteralDeltaAt k index) s).trans
    (Delta0Formula.satisfies_natLiteralDeltaAt
      k index (fun i => (s i).1))

@[simp]
theorem lmem_textbookNatCode_omegaLCarrier (k : Nat) :
    LMem (TextbookNatFormula.textbookNatCodeLCarrier k)
      omegaLCarrier := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode k)).mpr ⟨k, rfl⟩

@[simp]
theorem lmem_textbookNatCode_iff_lt (i n : Nat) :
    LMem (TextbookNatFormula.textbookNatCodeLCarrier i)
        (TextbookNatFormula.textbookNatCodeLCarrier n) <->
      i < n := by
  exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
    (natCode i) n).trans (by
      constructor
      · rintro ⟨j, hj, hji⟩
        exact (natCode_injective hji).symm ▸ hj
      · intro hi
        exact ⟨i, hi, rfl⟩)

theorem satisfies_codeGuardBody_lCarrier_natCode
    (literal : Nat) (bounded : Bool)
    (a key history output : LCarrier.{u}) (m n i j : Nat) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.codeGuardBody literal bounded)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          TextbookNatFormula.textbookNatCodeLCarrier literal] <->
      m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  cases bounded <;>
    simp [TextbookEFormula.codeGuardBody,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt,
      TextbookNatFormula.satisfies_textbookECodeFormula_lCarrier_natCode_iff,
      satisfies_natLiteralDeltaAt_lCarrier,
      lmem_textbookNatCode_omegaLCarrier,
      lmem_textbookNatCode_iff_lt,
      natCode_injective.eq_iff]

theorem satisfies_codeGuard_lCarrier_standard
    (literal : Nat) (bounded : Bool)
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.codeGuard literal bounded)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  rw [TextbookEFormula.codeGuard]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hassign (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hbody⟩
    rw [hassign] at hbody
    have hiOmega : iSet.1 ∈ omegaLCarrier.1 := hbody.1
    have hjOmega : jSet.1 ∈ omegaLCarrier.1 := hbody.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hiOmega with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hjOmega with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode literal : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        literal (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          tagSet]).mp hbody.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier literal :=
      Subtype.ext htagVal
    subst tagSet
    exact ⟨i, j,
      (satisfies_codeGuardBody_lCarrier_natCode
        literal bounded a key history output m n i j).mp hbody⟩
  · rintro ⟨i, j, hcode⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier literal, ?_⟩
    rw [hassign]
    exact (satisfies_codeGuardBody_lCarrier_natCode
      literal bounded a key history output m n i j).mpr hcode

end

end Model

end Constructible
