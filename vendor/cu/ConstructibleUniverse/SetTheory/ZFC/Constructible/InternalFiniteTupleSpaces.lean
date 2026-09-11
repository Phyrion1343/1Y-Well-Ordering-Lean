/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepOperationsLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalUnion

/-!
# The internal set of finite tuples

For a constructible set `a`, Replacement applied to the finite-function-space
formula produces the actual family

`{a^n | n in omega}`.

Its union is therefore an actual member of `L` containing exactly the
set-coded finite tuples from `a`.  The index-to-space map is represented by a
Kuratowski graph in `L`; an external `Nat -> ZFSet` is not used as that graph.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The uniform finite-power formula -/

/-- Reorder `[a,index,space]` as the input layout
`[index,a,space]` of `finiteFunctionSpaceGraph`. -/
def finiteTupleSpaceFormulaRename : Fin 3 -> Fin 3 :=
  ![1, 0, 2]

/-- Layout `[a,index,space]`: `index` is a standard natural-number code and
`space` is the set of all functions from `index` to `a`. -/
def finiteTupleSpaceFormula : FOFormula 3 :=
  FOFormula.rename finiteTupleSpaceFormulaRename
    Constructible.Model.finiteFunctionSpaceGraph

private theorem comp_finiteTupleSpaceFormulaRename
    (a index space : LCarrier.{u}) :
    (fun i => ![a, index, space] (finiteTupleSpaceFormulaRename i)) =
      ![index, a, space] := by
  funext i
  fin_cases i <;> rfl

/-- Exact `LCarrier` semantics at a standard natural-number index. -/
@[simp]
theorem satisfies_finiteTupleSpaceFormula_natCode_iff
    (a space : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem finiteTupleSpaceFormula
        ![a, Constructible.TextbookNatFormula.textbookNatCodeLCarrier n,
          space] <->
      space.1 = textbookTupleSpace a.1 n := by
  rw [finiteTupleSpaceFormula, FOFormula.satisfies_rename,
    comp_finiteTupleSpaceFormulaRename]
  simpa only [textbookTupleSpace] using
    (Constructible.Model.satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
      n a space)

/-- The finite power `a^n`, packaged as a genuine member of `L`. -/
def finiteTupleSpaceLCarrier (a : LCarrier.{u}) (n : Nat) :
    LCarrier.{u} :=
  ⟨textbookTupleSpace a.1 n,
    textbookTupleSpace_mem_L a.2 n⟩

@[simp]
theorem finiteTupleSpaceLCarrier_val (a : LCarrier.{u}) (n : Nat) :
    (finiteTupleSpaceLCarrier a n).1 = textbookTupleSpace a.1 n :=
  rfl

private theorem finiteTupleSpaceFormula_existsUnique
    (a index : LCarrier.{u})
    (hindex : index.1 ∈ (omegaLCarrier : LCarrier.{u}).1) :
    ExistsUnique fun space : LCarrier.{u} =>
      FOFormula.Satisfies LMem finiteTupleSpaceFormula
        ![a, index, space] := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
      hindex with ⟨n, hindexCode⟩
  have hindexEq :
      index =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact hindexCode
  subst index
  refine ⟨finiteTupleSpaceLCarrier a n, ?_, ?_⟩
  · exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a (finiteTupleSpaceLCarrier a n) n).mpr rfl
  · intro other hother
    apply Subtype.ext
    exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a other n).mp hother

private theorem finiteTupleSpaceFormula_assignment
    (a index space : LCarrier.{u}) :
    snoc (snoc ![a] index) space = ![a, index, space] := by
  funext i
  fin_cases i <;> rfl

/-! ## Replacement range and graph -/

/-- The internally represented data for the family `n |-> a^n`. -/
structure InternalFiniteTupleSpaceFamilyData (a : LCarrier.{u}) where
  graph : LCarrier.{u}
  family : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem graph
    (omegaLCarrier : LCarrier.{u}) family
  mem_family_iff : forall space : LCarrier.{u},
    space.1 ∈ family.1 <->
      exists n : Nat, space = finiteTupleSpaceLCarrier a n
  graphValue_iff : forall index space : LCarrier.{u},
    GraphValue LMem graph index space <->
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem finiteTupleSpaceFormula
          ![a, index, space]

/-- Replacement produces both the actual range and the actual Kuratowski
graph of the finite-power operation. -/
theorem exists_internalFiniteTupleSpaceFamilyData
    (a : LCarrier.{u}) :
    Nonempty (InternalFiniteTupleSpaceFamilyData a) := by
  let params : Tuple LCarrier.{u} 1 := ![a]
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        ExistsUnique fun space : LCarrier.{u} =>
          FOFormula.Satisfies LMem finiteTupleSpaceFormula
            (snoc (snoc params index) space) := by
    intro index hindex
    simpa only [params, finiteTupleSpaceFormula_assignment] using
      finiteTupleSpaceFormula_existsUnique a index hindex
  rcases Constructible.Model.exists_replacementLCarrier
      finiteTupleSpaceFormula params omegaLCarrier hfun with
    ⟨family, hfamily⟩
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      finiteTupleSpaceFormula params omegaLCarrier hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall index space : LCarrier.{u},
      GraphValue LMem graph index space <->
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
          FOFormula.Satisfies LMem finiteTupleSpaceFormula
            ![a, index, space] := by
    intro index space
    constructor
    · rintro ⟨pair, hpairGraph, hpairIS⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨index', hindex', space', hspace', hpairEq⟩
      have hpairISEq :=
        (isKuratowskiPairOf_lCarrier_iff pair index space).mp hpairIS
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairISEq)
      have hindexEq : index' = index := Subtype.ext hcoordinates.1
      have hspaceEq : space' = space := Subtype.ext hcoordinates.2
      subst index'
      subst space'
      simpa only [params, finiteTupleSpaceFormula_assignment] using
        And.intro hindex' hspace'
    · rintro ⟨hindex, hspace⟩
      let pair := orderedPairLCarrier index space
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        refine ⟨index, hindex, space, ?_, rfl⟩
        simpa only [params, finiteTupleSpaceFormula_assignment] using hspace
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair index space).mpr rfl
  have hbetween : IsGraphBetween LMem graph omegaLCarrier family := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨index, hindex, space, hspace, hpairEq⟩
    have hspaceFamily : space.1 ∈ family.1 :=
      (hfamily space).mpr ⟨index, hindex, hspace⟩
    exact ⟨index, hindex, space, hspaceFamily,
      (isKuratowskiPairOf_lCarrier_iff pair index space).mpr hpairEq⟩
  have htotal : forall index : LCarrier.{u},
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        HasUniqueImage LMem graph index family := by
    intro index hindex
    rcases hfun index hindex with ⟨space, hspace, hspaceUnique⟩
    have hspaceFamily : space.1 ∈ family.1 :=
      (hfamily space).mpr ⟨index, hindex, hspace⟩
    refine ⟨space, hspaceFamily,
      (hvalue index space).mpr ⟨hindex, by
        simpa only [params, finiteTupleSpaceFormula_assignment] using
          hspace⟩, ?_⟩
    intro other _hotherFamily hindexOther
    apply hspaceUnique other
    have hother := (hvalue index other).mp hindexOther |>.2
    simpa only [params, finiteTupleSpaceFormula_assignment] using hother
  refine ⟨{
    graph := graph
    family := family
    isFunctionGraph := ⟨hbetween, htotal⟩
    mem_family_iff := ?_
    graphValue_iff := hvalue
  }⟩
  intro space
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hspace⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq :
        index =
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexCode
    subst index
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a space n).mp (by
        simpa only [params, finiteTupleSpaceFormula_assignment] using hspace)
  · rintro ⟨n, rfl⟩
    let index :=
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier n
    refine ⟨index, ?_, ?_⟩
    · change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · simpa only [params, index, finiteTupleSpaceFormula_assignment] using
        (satisfies_finiteTupleSpaceFormula_natCode_iff
          a (finiteTupleSpaceLCarrier a n) n).mpr rfl

/-- A canonical choice of the Replacement data.  Its public API is solely
the extensional specification proved above. -/
noncomputable def internalFiniteTupleSpaceFamilyData
    (a : LCarrier.{u}) : InternalFiniteTupleSpaceFamilyData a :=
  Classical.choice (exists_internalFiniteTupleSpaceFamilyData a)

/-- The genuine internal set of all finite tuple graphs over `a`. -/
noncomputable def internalFiniteTupleSpaces (a : LCarrier.{u}) :
    LCarrier.{u} :=
  sUnionLCarrier (internalFiniteTupleSpaceFamilyData a).family

@[simp]
theorem mem_internalFiniteTupleSpaces_iff
    (a z : LCarrier.{u}) :
    z.1 ∈ (internalFiniteTupleSpaces a).1 <->
      exists n : Nat, z.1 ∈ (finiteTupleSpaceLCarrier a n).1 := by
  rw [internalFiniteTupleSpaces, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨space, hspaceFamily, hz⟩
    rcases (internalFiniteTupleSpaceFamilyData a).mem_family_iff
        space |>.mp hspaceFamily with ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨finiteTupleSpaceLCarrier a n,
      (internalFiniteTupleSpaceFamilyData a).mem_family_iff
        (finiteTupleSpaceLCarrier a n) |>.mpr ⟨n, rfl⟩, hz⟩

end

end Constructible.ContinuumFormula
