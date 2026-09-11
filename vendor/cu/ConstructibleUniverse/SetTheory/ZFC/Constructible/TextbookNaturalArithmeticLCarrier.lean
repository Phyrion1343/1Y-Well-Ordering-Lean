/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomainLCarrier

/-!
# Natural-arithmetic witnesses in the constructible universe

The textbook formulas for addition, multiplication, and exponentiation use
finite function graphs as their recursion certificates.  This file proves
that their canonical certificates are actual elements of `L`.  These are the
witness-closure facts needed to establish exact `LCarrier` semantics for the
three formulas and, subsequently, for the prime-power code used by `E`.
-/

@[expose] public section

universe u

namespace Constructible.TextbookNatFormula

noncomputable section

open FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem

@[simp]
theorem satisfies_natLiteralDeltaAt_toFO_lCarrier
    (k : Nat) {n : Nat} (index : Fin n)
    (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.natLiteralDeltaAt k index).toFO s <->
      (s index).1 = (natCode k : ZFSet.{u}) := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.natLiteralDeltaAt k index) s).trans
    (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
      k index (fun i => (s i).1))

@[simp]
theorem satisfies_natPowFormulaAt_lCarrier {n : Nat}
    (omega base exponent output : Fin n)
    (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (natPowFormulaAt omega base exponent output) s <->
      FOFormula.Satisfies LMem natPowFormula
        ![s omega, s base, s exponent, s output] := by
  rw [natPowFormulaAt, FOFormula.satisfies_rename,
    comp_natPowParametersAt]

/-- A standard natural-number code, packaged as an element of `LCarrier`. -/
def textbookNatCodeLCarrier (n : Nat) : Model.LCarrier.{u} :=
  ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem textbookNatCodeLCarrier_val (n : Nat) :
    (textbookNatCodeLCarrier n : Model.LCarrier.{u}).1 = natCode n :=
  rfl

/-- The canonical finite graph certifying natural-number addition belongs to
the constructible universe. -/
theorem natAddCanonicalGraph_mem_L (a b : Nat) :
    natAddCanonicalGraph a b ∈ L := by
  exact textbookTupleGraph_mem_L omega_mem_L (natAddCanonicalTuple a b)

/-- The canonical finite graph certifying natural-number multiplication
belongs to the constructible universe. -/
theorem natMulCanonicalGraph_mem_L (a b : Nat) :
    natMulCanonicalGraph a b ∈ L := by
  exact textbookTupleGraph_mem_L omega_mem_L (natMulCanonicalTuple a b)

/-- The canonical finite graph certifying natural-number exponentiation
belongs to the constructible universe. -/
theorem natPowCanonicalGraph_mem_L (base exponent : Nat) :
    natPowCanonicalGraph base exponent ∈ L := by
  exact textbookTupleGraph_mem_L omega_mem_L
    (natPowCanonicalTuple base exponent)

private def natAddCanonicalGraphL (a b : Nat) : Model.LCarrier.{u} :=
  ⟨natAddCanonicalGraph a b, natAddCanonicalGraph_mem_L a b⟩

private def natMulCanonicalGraphL (a b : Nat) : Model.LCarrier.{u} :=
  ⟨natMulCanonicalGraph a b, natMulCanonicalGraph_mem_L a b⟩

private def natPowCanonicalGraphL
    (base exponent : Nat) : Model.LCarrier.{u} :=
  ⟨natPowCanonicalGraph base exponent,
    natPowCanonicalGraph_mem_L base exponent⟩

set_option maxHeartbeats 800000

/-! ## Exact addition semantics -/

/-- The membership-language addition formula has its intended semantics in
`LCarrier` on standard natural-number codes. -/
@[simp]
theorem satisfies_natAddFormula_lCarrier_natCode_iff
    (a b : Nat) (z : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natAddFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          textbookNatCodeLCarrier b, z] <->
      z.1 = natCode (a + b) := by
  let s : Tuple Model.LCarrier.{u} 4 :=
    ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
      textbookNatCodeLCarrier b, z]
  change
    ((FOFormula.Satisfies LMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (textbookNatCodeLCarrier a).1 ∈ Model.omegaLCarrier.1 /\
      (textbookNatCodeLCarrier b).1 ∈ Model.omegaLCarrier.1 /\
      z.1 ∈ Model.omegaLCarrier.1 /\
      ∃ ySucc : Model.LCarrier.{u},
        FOFormula.Satisfies LMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        ∃ graph : Model.LCarrier.{u},
          FOFormula.Satisfies LMem natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph)) <-> _)
  constructor
  · rintro ⟨_homega, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySuccFormula, graph, hgraphFormula⟩
    have hySuccAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc)).mp hySuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hySuccAmbient
    have hySucc : ySucc.1 = natCode (b + 1) := by
      have hraw : ySucc.1 = insert (natCode b) (natCode b) := by
        change ySucc.1 = insert (natCode b) (natCode b) at hySuccAmbient
        exact hySuccAmbient
      exact hraw.trans (natCode_succ_eq_insert b).symm
    have hgraphAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute natAddGraphDelta
        (snoc (snoc s ySucc) graph)).mp hgraphFormula
    rw [Delta0Formula.satisfies_toFO] at hgraphAmbient
    have hassign : (fun i => (snoc (snoc s ySucc) graph i).1) =
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
          z.1, ySucc.1, graph.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphAmbient
    exact natAddGraphDelta_output_unique
      a b z.1 ySucc.1 graph.1 hySucc hgraphAmbient
  · intro hz
    let ySucc : Model.LCarrier.{u} := textbookNatCodeLCarrier (b + 1)
    let graph : Model.LCarrier.{u} := natAddCanonicalGraphL a b
    refine ⟨(Model.satisfies_standardOmegaAt_lCarrier
      (0 : Fin 4) s).mpr rfl, ?_, ?_, ?_, ySucc, ?_, graph, ?_⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩
    · rw [hz]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + b))).mpr ⟨a + b, rfl⟩
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      change (natCode (b + 1) : ZFSet.{u}) =
        insert (natCode b) (natCode b)
      exact natCode_succ_eq_insert b
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        natAddGraphDelta (snoc (snoc s ySucc) graph)).mpr
      rw [Delta0Formula.satisfies_toFO]
      have hassign : (fun i => (snoc (snoc s ySucc) graph i).1) =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
            z.1, natCode (b + 1), natAddCanonicalGraph a b] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign, hz]
      exact natAddCanonicalGraph_satisfies a b

/-! ## Multiplication transition semantics -/

@[simp]
theorem satisfies_natMulTransition_lCarrier
    (omega x y z ySucc graph : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natMulTransition
        ![omega, x, y, z, ySucc, graph] <->
      ∀ k : Model.LCarrier.{u}, k.1 ∈ y.1 ->
        insert k.1 k.1 ∈ ySucc.1 /\
        ∃ value : Model.LCarrier.{u}, value.1 ∈ omega.1 /\
          ZFSet.pair k.1 value.1 ∈ graph.1 /\
          ∃ nextValue : Model.LCarrier.{u},
            nextValue.1 ∈ omega.1 /\
            ZFSet.pair (insert k.1 k.1) nextValue.1 ∈ graph.1 /\
            FOFormula.Satisfies LMem natAddFormula
              ![omega, value, x, nextValue] := by
  simp only [natMulTransition, natMulTransitionAt,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies,
    FOFormula.satisfies_rename, snoc_castSucc,
    comp_natMulAddRenameAt]
  constructor
  · intro h k hk
    rcases h k hk with
      ⟨kSucc, hkSuccDomain, hkSucc, value, hvalueOmega,
        hvalue, nextValue, hnextOmega, hnext, hadd⟩
    change kSucc.1 ∈ ySucc.1 at hkSuccDomain
    change value.1 ∈ omega.1 at hvalueOmega
    change nextValue.1 ∈ omega.1 at hnextOmega
    have hkSuccAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc ![omega, x, y, z, ySucc, graph] k) kSucc)).mp
          hkSucc
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hkSuccAmbient
    have hkSuccEq : kSucc.1 = insert k.1 k.1 := by
      simpa only [snoc_last, snoc_castSucc] using hkSuccAmbient
    have hvalueAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc ![omega, x, y, z, ySucc, graph]
          k) kSucc) value)).mp hvalue
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hvalueAmbient
    have hvalueGraph : ZFSet.pair k.1 value.1 ∈ graph.1 := by
      change ZFSet.pair k.1 value.1 ∈ graph.1 at hvalueAmbient
      exact hvalueAmbient
    have hnextAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc
          ![omega, x, y, z, ySucc, graph] k) kSucc) value)
          nextValue)).mp hnext
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hnextAmbient
    have hnextGraph : ZFSet.pair kSucc.1 nextValue.1 ∈ graph.1 := by
      change ZFSet.pair kSucc.1 nextValue.1 ∈ graph.1 at hnextAmbient
      exact hnextAmbient
    rw [hkSuccEq] at hkSuccDomain hnextGraph
    exact ⟨hkSuccDomain, value, hvalueOmega, hvalueGraph,
      nextValue, hnextOmega, hnextGraph, by simpa using hadd⟩
  · intro h k hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalue,
        nextValue, hnextOmega, hnext, hadd⟩
    let kSucc : Model.LCarrier.{u} :=
      ⟨insert k.1 k.1, textbookInsert_mem_L k.2 k.2⟩
    refine ⟨kSucc, hkSuccDomain, ?_, value, hvalueOmega,
      ?_, nextValue, hnextOmega, ?_, by simpa using hadd⟩
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc ![omega, x, y, z, ySucc, graph] k) kSucc)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      rfl
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc ![omega, x, y, z, ySucc, graph]
          k) kSucc) value)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair k.1 value.1 ∈ graph.1
      exact hvalue
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc
          ![omega, x, y, z, ySucc, graph] k) kSucc) value)
          nextValue)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair (insert k.1 k.1) nextValue.1 ∈ graph.1
      exact hnext

theorem satisfies_natMulGraphFormula_lCarrier_iff_ambient
    (a : Nat) (y z ySucc graph : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natMulGraphFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          y, z, ySucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
          y.1, z.1, ySucc.1, graph.1] := by
  change
    ((FOFormula.Satisfies LMem natMulGraphShapeDelta.toFO
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          y, z, ySucc, graph] /\
      FOFormula.Satisfies LMem natMulTransition
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          y, z, ySucc, graph]) <->
      (FOFormula.Satisfies Delta0Formula.ZFMem
          natMulGraphShapeDelta.toFO
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            y.1, z.1, ySucc.1, graph.1] /\
        FOFormula.Satisfies Delta0Formula.ZFMem natMulTransition
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            y.1, z.1, ySucc.1, graph.1]))
  have hshape :
      FOFormula.Satisfies LMem natMulGraphShapeDelta.toFO
          ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
            y, z, ySucc, graph] <->
        FOFormula.Satisfies Delta0Formula.ZFMem
          natMulGraphShapeDelta.toFO
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            y.1, z.1, ySucc.1, graph.1] := by
    have habsolute := Delta0Formula.satisfies_toFO_lCarrier_absolute
      natMulGraphShapeDelta
      ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
        y, z, ySucc, graph]
    have hassign :
        (fun i =>
          (![Model.omegaLCarrier, textbookNatCodeLCarrier a,
            y, z, ySucc, graph] i).1) =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            y.1, z.1, ySucc.1, graph.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at habsolute
    exact habsolute
  rw [hshape]
  apply and_congr Iff.rfl
  constructor
  · intro htransition
    apply (satisfies_natMulTransition
      (Ordinal.omega0.toZFSet : ZFSet.{u}) (natCode a)
      y.1 z.1 ySucc.1 graph.1).mpr
    intro k hk
    let kL : Model.LCarrier.{u} :=
      ⟨k, mem_L_of_mem hk y.2⟩
    rcases (satisfies_natMulTransition_lCarrier
      Model.omegaLCarrier (textbookNatCodeLCarrier a)
      y z ySucc graph).mp htransition kL hk with
      ⟨hkSucc, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, hadd⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value.1).mp
        hvalueOmega with ⟨c, hc⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue.1).mp
        hnextOmega with ⟨d, hd⟩
    have haddEq : nextValue.1 = natCode (c + a) := by
      have hvalueEq : value = textbookNatCodeLCarrier c :=
        Subtype.ext hc
      rw [hvalueEq] at hadd
      exact (satisfies_natAddFormula_lCarrier_natCode_iff
        c a nextValue).mp hadd
    have haddAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), value.1,
            natCode a, nextValue.1] := by
      rw [hc, hd]
      apply (satisfies_natAddFormula_natCode_iff c a (natCode d)).mpr
      simpa only [hd] using haddEq
    exact ⟨hkSucc, value.1, hvalueOmega, hvalueGraph,
      nextValue.1, hnextOmega, hnextGraph, haddAmbient⟩
  · intro htransition
    apply (satisfies_natMulTransition_lCarrier
      Model.omegaLCarrier (textbookNatCodeLCarrier a)
      y z ySucc graph).mpr
    intro k hk
    rcases (satisfies_natMulTransition
      (Ordinal.omega0.toZFSet : ZFSet.{u}) (natCode a)
      y.1 z.1 ySucc.1 graph.1).mp htransition k.1 hk with
      ⟨hkSucc, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, haddAmbient⟩
    let valueL : Model.LCarrier.{u} :=
      ⟨value, mem_L_of_mem hvalueOmega omega_mem_L⟩
    let nextValueL : Model.LCarrier.{u} :=
      ⟨nextValue, mem_L_of_mem hnextOmega omega_mem_L⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hvalueOmega with ⟨c, hc⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hnextOmega with ⟨d, hd⟩
    have haddEq : (natCode d : ZFSet.{u}) = natCode (c + a) :=
      (satisfies_natAddFormula_natCode_iff c a (natCode d)).mp
        (by simpa only [hc, hd] using haddAmbient)
    have hadd : FOFormula.Satisfies LMem natAddFormula
        ![Model.omegaLCarrier, valueL,
          textbookNatCodeLCarrier a, nextValueL] := by
      have hvalueEq : valueL = textbookNatCodeLCarrier c :=
        Subtype.ext hc
      rw [hvalueEq]
      apply (satisfies_natAddFormula_lCarrier_natCode_iff
        c a nextValueL).mpr
      simpa only [nextValueL, hd] using haddEq
    exact ⟨hkSucc, valueL, hvalueOmega, hvalueGraph,
      nextValueL, hnextOmega, hnextGraph, hadd⟩

/-! ## Exact multiplication semantics -/

/-- The membership-language multiplication formula has its intended
semantics in `LCarrier` on standard natural-number codes. -/
@[simp]
theorem satisfies_natMulFormula_lCarrier_natCode_iff
    (a b : Nat) (z : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natMulFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          textbookNatCodeLCarrier b, z] <->
      z.1 = natCode (a * b) := by
  let s : Tuple Model.LCarrier.{u} 4 :=
    ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
      textbookNatCodeLCarrier b, z]
  change
    ((FOFormula.Satisfies LMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (textbookNatCodeLCarrier a).1 ∈ Model.omegaLCarrier.1 /\
      (textbookNatCodeLCarrier b).1 ∈ Model.omegaLCarrier.1 /\
      z.1 ∈ Model.omegaLCarrier.1 /\
      ∃ ySucc : Model.LCarrier.{u},
        FOFormula.Satisfies LMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        ∃ graph : Model.LCarrier.{u},
          FOFormula.Satisfies LMem natMulGraphFormula
            (snoc (snoc s ySucc) graph)) <-> _)
  constructor
  · rintro ⟨_homega, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySuccFormula, graph, hgraphFormula⟩
    have hySuccAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc)).mp hySuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hySuccAmbient
    have hySucc : ySucc.1 = natCode (b + 1) := by
      have hraw : ySucc.1 = insert (natCode b) (natCode b) := by
        change ySucc.1 = insert (natCode b) (natCode b) at hySuccAmbient
        exact hySuccAmbient
      exact hraw.trans (natCode_succ_eq_insert b).symm
    have hassign : snoc (snoc s ySucc) graph =
        ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
          textbookNatCodeLCarrier b, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphFormula
    have hgraphAmbient :=
      (satisfies_natMulGraphFormula_lCarrier_iff_ambient
        a (textbookNatCodeLCarrier b) z ySucc graph).mp hgraphFormula
    exact natMulGraphFormula_output_unique
      a b z.1 ySucc.1 graph.1 hySucc hgraphAmbient
  · intro hz
    let ySucc : Model.LCarrier.{u} := textbookNatCodeLCarrier (b + 1)
    let graph : Model.LCarrier.{u} := natMulCanonicalGraphL a b
    refine ⟨(Model.satisfies_standardOmegaAt_lCarrier
      (0 : Fin 4) s).mpr rfl, ?_, ?_, ?_, ySucc, ?_, graph, ?_⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩
    · rw [hz]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * b))).mpr ⟨a * b, rfl⟩
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      change (natCode (b + 1) : ZFSet.{u}) =
        insert (natCode b) (natCode b)
      exact natCode_succ_eq_insert b
    · have hassign : snoc (snoc s ySucc) graph =
          ![Model.omegaLCarrier, textbookNatCodeLCarrier a,
            textbookNatCodeLCarrier b, z, ySucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign]
      apply (satisfies_natMulGraphFormula_lCarrier_iff_ambient
        a (textbookNatCodeLCarrier b) z ySucc graph).mpr
      rw [hz]
      exact natMulCanonicalGraph_satisfies a b

/-! ## Exponentiation transition semantics -/

@[simp]
theorem satisfies_natPowTransition_lCarrier
    (omega base exponent output exponentSucc graph : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] <->
      ∀ k : Model.LCarrier.{u}, k.1 ∈ exponent.1 ->
        insert k.1 k.1 ∈ exponentSucc.1 /\
        ∃ value : Model.LCarrier.{u}, value.1 ∈ omega.1 /\
          ZFSet.pair k.1 value.1 ∈ graph.1 /\
          ∃ nextValue : Model.LCarrier.{u},
            nextValue.1 ∈ omega.1 /\
            ZFSet.pair (insert k.1 k.1) nextValue.1 ∈ graph.1 /\
            FOFormula.Satisfies LMem natMulFormula
              ![omega, value, base, nextValue] := by
  simp only [natPowTransition, natPowTransitionAt,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies,
    FOFormula.satisfies_rename, snoc_castSucc,
    comp_natPowMulRenameAt]
  constructor
  · intro h k hk
    rcases h k hk with
      ⟨kSucc, hkSuccDomain, hkSucc, value, hvalueOmega,
        hvalue, nextValue, hnextOmega, hnext, hmul⟩
    change kSucc.1 ∈ exponentSucc.1 at hkSuccDomain
    change value.1 ∈ omega.1 at hvalueOmega
    change nextValue.1 ∈ omega.1 at hnextOmega
    have hkSuccAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc)).mp hkSucc
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hkSuccAmbient
    have hkSuccEq : kSucc.1 = insert k.1 k.1 := by
      simpa only [snoc_last, snoc_castSucc] using hkSuccAmbient
    have hvalueAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc) value)).mp hvalue
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hvalueAmbient
    have hvalueGraph : ZFSet.pair k.1 value.1 ∈ graph.1 := by
      change ZFSet.pair k.1 value.1 ∈ graph.1 at hvalueAmbient
      exact hvalueAmbient
    have hnextAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc) value) nextValue)).mp hnext
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hnextAmbient
    have hnextGraph : ZFSet.pair kSucc.1 nextValue.1 ∈ graph.1 := by
      change ZFSet.pair kSucc.1 nextValue.1 ∈ graph.1 at hnextAmbient
      exact hnextAmbient
    rw [hkSuccEq] at hkSuccDomain hnextGraph
    exact ⟨hkSuccDomain, value, hvalueOmega, hvalueGraph,
      nextValue, hnextOmega, hnextGraph, by simpa using hmul⟩
  · intro h k hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalue,
        nextValue, hnextOmega, hnext, hmul⟩
    let kSucc : Model.LCarrier.{u} :=
      ⟨insert k.1 k.1, textbookInsert_mem_L k.2 k.2⟩
    refine ⟨kSucc, hkSuccDomain, ?_, value, hvalueOmega,
      ?_, nextValue, hnextOmega, ?_, by simpa using hmul⟩
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      rfl
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc) value)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair k.1 value.1 ∈ graph.1
      exact hvalue
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc
          ![omega, base, exponent, output, exponentSucc, graph]
          k) kSucc) value) nextValue)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair (insert k.1 k.1) nextValue.1 ∈ graph.1
      exact hnext

theorem satisfies_natPowGraphFormula_lCarrier_iff_ambient
    (base : Nat)
    (exponent output exponentSucc graph : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natPowGraphFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
          exponent, output, exponentSucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          exponent.1, output.1, exponentSucc.1, graph.1] := by
  change
    ((FOFormula.Satisfies LMem natPowGraphShapeDelta.toFO
        ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
          exponent, output, exponentSucc, graph] /\
      FOFormula.Satisfies LMem natPowTransition
        ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
          exponent, output, exponentSucc, graph]) <->
      (FOFormula.Satisfies Delta0Formula.ZFMem
          natPowGraphShapeDelta.toFO
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
            exponent.1, output.1, exponentSucc.1, graph.1] /\
        FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
            exponent.1, output.1, exponentSucc.1, graph.1]))
  have hshape :
      FOFormula.Satisfies LMem natPowGraphShapeDelta.toFO
          ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
            exponent, output, exponentSucc, graph] <->
        FOFormula.Satisfies Delta0Formula.ZFMem
          natPowGraphShapeDelta.toFO
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
            exponent.1, output.1, exponentSucc.1, graph.1] := by
    have habsolute := Delta0Formula.satisfies_toFO_lCarrier_absolute
      natPowGraphShapeDelta
      ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
        exponent, output, exponentSucc, graph]
    have hassign :
        (fun i =>
          (![Model.omegaLCarrier, textbookNatCodeLCarrier base,
            exponent, output, exponentSucc, graph] i).1) =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
            exponent.1, output.1, exponentSucc.1, graph.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at habsolute
    exact habsolute
  rw [hshape]
  apply and_congr Iff.rfl
  constructor
  · intro htransition
    apply (satisfies_natPowTransition
      (Ordinal.omega0.toZFSet : ZFSet.{u}) (natCode base)
      exponent.1 output.1 exponentSucc.1 graph.1).mpr
    intro k hk
    let kL : Model.LCarrier.{u} :=
      ⟨k, mem_L_of_mem hk exponent.2⟩
    rcases (satisfies_natPowTransition_lCarrier
      Model.omegaLCarrier (textbookNatCodeLCarrier base)
      exponent output exponentSucc graph).mp htransition kL hk with
      ⟨hkSucc, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, hmul⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value.1).mp
        hvalueOmega with ⟨c, hc⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue.1).mp
        hnextOmega with ⟨d, hd⟩
    have hmulEq : nextValue.1 = natCode (c * base) := by
      have hvalueEq : value = textbookNatCodeLCarrier c :=
        Subtype.ext hc
      rw [hvalueEq] at hmul
      exact (satisfies_natMulFormula_lCarrier_natCode_iff
        c base nextValue).mp hmul
    have hmulAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), value.1,
            natCode base, nextValue.1] := by
      rw [hc, hd]
      apply (satisfies_natMulFormula_natCode_iff
        c base (natCode d)).mpr
      simpa only [hd] using hmulEq
    exact ⟨hkSucc, value.1, hvalueOmega, hvalueGraph,
      nextValue.1, hnextOmega, hnextGraph, hmulAmbient⟩
  · intro htransition
    apply (satisfies_natPowTransition_lCarrier
      Model.omegaLCarrier (textbookNatCodeLCarrier base)
      exponent output exponentSucc graph).mpr
    intro k hk
    rcases (satisfies_natPowTransition
      (Ordinal.omega0.toZFSet : ZFSet.{u}) (natCode base)
      exponent.1 output.1 exponentSucc.1 graph.1).mp
        htransition k.1 hk with
      ⟨hkSucc, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, hmulAmbient⟩
    let valueL : Model.LCarrier.{u} :=
      ⟨value, mem_L_of_mem hvalueOmega omega_mem_L⟩
    let nextValueL : Model.LCarrier.{u} :=
      ⟨nextValue, mem_L_of_mem hnextOmega omega_mem_L⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hvalueOmega with ⟨c, hc⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hnextOmega with ⟨d, hd⟩
    have hmulEq : (natCode d : ZFSet.{u}) = natCode (c * base) :=
      (satisfies_natMulFormula_natCode_iff
        c base (natCode d)).mp
          (by simpa only [hc, hd] using hmulAmbient)
    have hmul : FOFormula.Satisfies LMem natMulFormula
        ![Model.omegaLCarrier, valueL,
          textbookNatCodeLCarrier base, nextValueL] := by
      have hvalueEq : valueL = textbookNatCodeLCarrier c :=
        Subtype.ext hc
      rw [hvalueEq]
      apply (satisfies_natMulFormula_lCarrier_natCode_iff
        c base nextValueL).mpr
      simpa only [nextValueL, hd] using hmulEq
    exact ⟨hkSucc, valueL, hvalueOmega, hvalueGraph,
      nextValueL, hnextOmega, hnextGraph, hmul⟩

/-! ## Exact exponentiation semantics -/

/-- The membership-language exponentiation formula has its intended
semantics in `LCarrier` on standard natural-number codes. -/
@[simp]
theorem satisfies_natPowFormula_lCarrier_natCode_iff
    (base exponent : Nat) (output : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem natPowFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
          textbookNatCodeLCarrier exponent, output] <->
      output.1 = natCode (base ^ exponent) := by
  let s : Tuple Model.LCarrier.{u} 4 :=
    ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
      textbookNatCodeLCarrier exponent, output]
  change
    ((FOFormula.Satisfies LMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (textbookNatCodeLCarrier base).1 ∈ Model.omegaLCarrier.1 /\
      (textbookNatCodeLCarrier exponent).1 ∈ Model.omegaLCarrier.1 /\
      output.1 ∈ Model.omegaLCarrier.1 /\
      ∃ exponentSucc : Model.LCarrier.{u},
        FOFormula.Satisfies LMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s exponentSucc) /\
        ∃ graph : Model.LCarrier.{u},
          FOFormula.Satisfies LMem natPowGraphFormula
            (snoc (snoc s exponentSucc) graph)) <-> _)
  constructor
  · rintro ⟨_homega, _hbaseOmega, _hexponentOmega, _houtputOmega,
      exponentSucc, hexponentSuccFormula, graph, hgraphFormula⟩
    have hexponentSuccAmbient :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s exponentSucc)).mp hexponentSuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hexponentSuccAmbient
    have hexponentSucc : exponentSucc.1 = natCode (exponent + 1) := by
      have hraw : exponentSucc.1 =
          insert (natCode exponent) (natCode exponent) := by
        change exponentSucc.1 =
          insert (natCode exponent) (natCode exponent) at hexponentSuccAmbient
        exact hexponentSuccAmbient
      exact hraw.trans (natCode_succ_eq_insert exponent).symm
    have hassign : snoc (snoc s exponentSucc) graph =
        ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
          textbookNatCodeLCarrier exponent, output,
          exponentSucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphFormula
    have hgraphAmbient :=
      (satisfies_natPowGraphFormula_lCarrier_iff_ambient
        base (textbookNatCodeLCarrier exponent) output
        exponentSucc graph).mp hgraphFormula
    exact natPowGraphFormula_output_unique
      base exponent output.1 exponentSucc.1 graph.1
        hexponentSucc hgraphAmbient
  · intro houtput
    let exponentSucc : Model.LCarrier.{u} :=
      textbookNatCodeLCarrier (exponent + 1)
    let graph : Model.LCarrier.{u} :=
      natPowCanonicalGraphL base exponent
    refine ⟨(Model.satisfies_standardOmegaAt_lCarrier
      (0 : Fin 4) s).mpr rfl, ?_, ?_, ?_, exponentSucc, ?_, graph, ?_⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode base)).mpr ⟨base, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩
    · rw [houtput]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s exponentSucc)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      change (natCode (exponent + 1) : ZFSet.{u}) =
        insert (natCode exponent) (natCode exponent)
      exact natCode_succ_eq_insert exponent
    · have hassign : snoc (snoc s exponentSucc) graph =
          ![Model.omegaLCarrier, textbookNatCodeLCarrier base,
            textbookNatCodeLCarrier exponent, output,
            exponentSucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign]
      apply (satisfies_natPowGraphFormula_lCarrier_iff_ambient
        base (textbookNatCodeLCarrier exponent) output
        exponentSucc graph).mpr
      rw [houtput]
      exact natPowCanonicalGraph_satisfies base exponent

/-! ## Exact semantics of the textbook prime-power code -/

/-- The pure membership-language formula for
`2 ^ i * 3 ^ j * 5 ^ tag` has its exact intended semantics in `LCarrier`.
All seven arithmetic witnesses are constructed internally as elements of
`L`; the theorem does not replace the object-language graph by an external
decoder. -/
@[simp]
theorem satisfies_textbookECodeFormula_lCarrier_natCode_iff
    (i j tag : Nat) (m : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookECodeFormula
        ![Model.omegaLCarrier, textbookNatCodeLCarrier i,
          textbookNatCodeLCarrier j, textbookNatCodeLCarrier tag, m] <->
      m.1 = natCode (textbookECode i j tag) := by
  let s : Tuple Model.LCarrier.{u} 5 :=
    ![Model.omegaLCarrier, textbookNatCodeLCarrier i,
      textbookNatCodeLCarrier j, textbookNatCodeLCarrier tag, m]
  change FOFormula.Satisfies LMem textbookECodeFormula s <-> _
  rw [textbookECodeFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨two, htwoFormula, htail⟩
    have htwo : two = textbookNatCodeLCarrier 2 := by
      apply Subtype.ext
      exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
        2 (5 : Fin 6) (snoc s two)).mp htwoFormula
    rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨three, hthreeFormula, htail⟩
    have hthree : three = textbookNatCodeLCarrier 3 := by
      apply Subtype.ext
      exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
        3 (6 : Fin 7) (snoc (snoc s two) three)).mp hthreeFormula
    rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨five, hfiveFormula, htail⟩
    have hfive : five = textbookNatCodeLCarrier 5 := by
      apply Subtype.ext
      exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
        5 (7 : Fin 8)
        (snoc (snoc (snoc s two) three) five)).mp hfiveFormula
    rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powTwo, hpowTwoFormula, htail⟩
    have hpowTwo : FOFormula.Satisfies LMem natPowFormula
        ![Model.omegaLCarrier, two, textbookNatCodeLCarrier i,
          powTwo] := by
      rw [satisfies_natPowFormulaAt_lCarrier,
        textbookECode_powTwo_assignment] at hpowTwoFormula
      exact hpowTwoFormula
    rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powThree, hpowThreeFormula, htail⟩
    have hpowThree : FOFormula.Satisfies LMem natPowFormula
        ![Model.omegaLCarrier, three, textbookNatCodeLCarrier j,
          powThree] := by
      rw [satisfies_natPowFormulaAt_lCarrier,
        textbookECode_powThree_assignment] at hpowThreeFormula
      exact hpowThreeFormula
    rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powFive, hpowFiveFormula, htail⟩
    have hpowFive : FOFormula.Satisfies LMem natPowFormula
        ![Model.omegaLCarrier, five, textbookNatCodeLCarrier tag,
          powFive] := by
      rw [satisfies_natPowFormulaAt_lCarrier,
        textbookECode_powFive_assignment] at hpowFiveFormula
      exact hpowFiveFormula
    rw [textbookECodeAfterPowFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨product, hfinalConjunction⟩
    rw [textbookECodeFinalFormula, FOFormula.Satisfies] at hfinalConjunction
    rcases hfinalConjunction with ⟨hproductFormula, hfinalFormula⟩
    have hproduct : FOFormula.Satisfies LMem natMulFormula
        ![Model.omegaLCarrier, powTwo, powThree, product] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_product_assignment] at hproductFormula
      exact hproductFormula
    have hfinal : FOFormula.Satisfies LMem natMulFormula
        ![Model.omegaLCarrier, product, powFive, m] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_final_assignment] at hfinalFormula
      exact hfinalFormula
    subst two
    subst three
    subst five
    have hpowTwo' :
        powTwo = textbookNatCodeLCarrier (2 ^ i) := by
      apply Subtype.ext
      exact (satisfies_natPowFormula_lCarrier_natCode_iff
        2 i powTwo).mp hpowTwo
    have hpowThree' :
        powThree = textbookNatCodeLCarrier (3 ^ j) := by
      apply Subtype.ext
      exact (satisfies_natPowFormula_lCarrier_natCode_iff
        3 j powThree).mp hpowThree
    have hpowFive' :
        powFive = textbookNatCodeLCarrier (5 ^ tag) := by
      apply Subtype.ext
      exact (satisfies_natPowFormula_lCarrier_natCode_iff
        5 tag powFive).mp hpowFive
    subst powTwo
    subst powThree
    subst powFive
    have hproduct' :
        product = textbookNatCodeLCarrier ((2 ^ i) * (3 ^ j)) := by
      apply Subtype.ext
      exact (satisfies_natMulFormula_lCarrier_natCode_iff
        (2 ^ i) (3 ^ j) product).mp hproduct
    subst product
    have hm : m.1 =
        (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfies_natMulFormula_lCarrier_natCode_iff
        ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mp hfinal
    simpa only [textbookECode, Nat.mul_assoc] using hm
  · intro hm
    have hm' : m.1 =
        (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hm
    refine ⟨textbookNatCodeLCarrier 2, ?_, ?_⟩
    · exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
        2 (5 : Fin 6) _).mpr rfl
    · rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies]
      refine ⟨textbookNatCodeLCarrier 3, ?_, ?_⟩
      · exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
          3 (6 : Fin 7) _).mpr rfl
      · rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies]
        refine ⟨textbookNatCodeLCarrier 5, ?_, ?_⟩
        · exact (satisfies_natLiteralDeltaAt_toFO_lCarrier
            5 (7 : Fin 8) _).mpr rfl
        · rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies]
          refine ⟨textbookNatCodeLCarrier (2 ^ i), ?_, ?_⟩
          · rw [satisfies_natPowFormulaAt_lCarrier,
              textbookECode_powTwo_assignment]
            exact (satisfies_natPowFormula_lCarrier_natCode_iff
              2 i (textbookNatCodeLCarrier (2 ^ i))).mpr rfl
          · rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies]
            refine ⟨textbookNatCodeLCarrier (3 ^ j), ?_, ?_⟩
            · rw [satisfies_natPowFormulaAt_lCarrier,
                textbookECode_powThree_assignment]
              exact (satisfies_natPowFormula_lCarrier_natCode_iff
                3 j (textbookNatCodeLCarrier (3 ^ j))).mpr rfl
            · rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies]
              refine ⟨textbookNatCodeLCarrier (5 ^ tag), ?_, ?_⟩
              · rw [satisfies_natPowFormulaAt_lCarrier,
                  textbookECode_powFive_assignment]
                exact (satisfies_natPowFormula_lCarrier_natCode_iff
                  5 tag (textbookNatCodeLCarrier (5 ^ tag))).mpr rfl
              · rw [textbookECodeAfterPowFiveFormula,
                  FOFormula.Satisfies]
                refine ⟨textbookNatCodeLCarrier
                  ((2 ^ i) * (3 ^ j)), ?_⟩
                rw [textbookECodeFinalFormula, FOFormula.Satisfies]
                constructor
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_product_assignment]
                  exact (satisfies_natMulFormula_lCarrier_natCode_iff
                    (2 ^ i) (3 ^ j)
                    (textbookNatCodeLCarrier
                      ((2 ^ i) * (3 ^ j)))).mpr rfl
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_final_assignment]
                  exact (satisfies_natMulFormula_lCarrier_natCode_iff
                    ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mpr hm'

end

end Constructible.TextbookNatFormula
