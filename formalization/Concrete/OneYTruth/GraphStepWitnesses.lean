import OneYTruth.GraphStepSoundness

/-! The actual eighteen candidate witnesses are constructible sets. -/

namespace OneYTruth.GraphStepMatrix

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open Constructible.Delta0Formula FormulaCode SyntaxDiagram BoundedEvaluation InternalNodes
open ConstructibleAssignmentCodes AssignmentLookup UniformSyntaxSource
open AtomicRelationGraphs InternalProducts ConstructibleDiagramSources ConstructibleSyntaxStages

universe u

noncomputable def canonicalRaw (κ η : Ordinal.{u}) (k : Nat) (U q S : ZFSet.{u}) : Tuple ZFSet.{u} 34 :=
  let c := ordinalIndexCode (η := η)
  let M := PredecessorGraph.interpretation k U c κ.toZFSet q
  let F := syntaxCodes (k := k) c
  let A := assignmentCodes U
  let P := scopedPairs (k := k) U c
  ![U,κ.toZFSet,(ordinalBound κ).val,A,lookupSet U,Ordinal.omega0.toZFSet,
    ∅,natCode 1,natCode 2,natCode 3,natCode 4,natCode 5,natCode 6,
    ZFSet.pair (natCode k) η.toZFSet,q,S,
    natCode k,η.toZFSet,F,pairProduct U U,pairProduct U (pairProduct U U),
    pairProduct (ZFSet.range c) (pairProduct U U),
    pairProduct (natCode k) (pairProduct U (pairProduct U U)),
    namedGraph c M,diagonalGraph M,
    pairProduct F A,P,atomSet (k := k) U c,quantifiedSet (k := k) U c,
    pairProduct P P,pairProduct P (pairProduct P P),
    implicationSet (k := k) U c,childrenSet (k := k) U c,trueAtomSet c M]

theorem canonicalRaw_mem_L (κ η : Ordinal.{u}) (k : Nat) (U q S : LCarrier.{u}) :
    ∀ i, canonicalRaw κ η k U.val q.val S.val i ∈ L := by
  let c := ordinalIndexCode (η := η)
  let M := PredecessorGraph.interpretation k U.val c κ.toZFSet q.val
  have hA : ZFSet.range c ∈ L := by rw [ordinal_range]; exact ordinal_toZFSet_mem_L _
  have hF := syntaxCodes_mem_L (k := k) hA
  have hAs := assignmentCodes_mem_L U.property
  have hLookup := lookupSet_mem_L U.property
  have hP := scopedPairs_mem_L (k := k) U.property hA
  have hAtom := atomSet_mem_L hP
  have hQuant := quantifiedSet_mem_L hP
  have hImp := implicationSet_mem_L hP
  have hChildren := childrenSet_mem_L U.property hP
  have hN : namedGraph c M ∈ L := PredecessorGraph.namedGraph_mem_L U.property hA q.property
  have hD : diagonalGraph M ∈ L := PredecessorGraph.diagonalGraph_mem_L c U.property
    (ordinal_toZFSet_mem_L κ) q.property
  have hTruth := trueAtomSet_mem_L_of_relation_graphs ordinalIndexCode_injective M
    (fun _ _ => Iff.rfl) U.property hA hN hD
  have hUU := pairProduct_mem_L U.property U.property
  have hUUU := pairProduct_mem_L U.property hUU
  have hNS := pairProduct_mem_L hA hUU
  have hDS := pairProduct_mem_L (natCode_mem_L k) hUUU
  have hCross := pairProduct_mem_L hF hAs
  have hSquare := pairProduct_mem_L hP hP
  have hTriples := pairProduct_mem_L hP hSquare
  intro i
  fin_cases i <;> first | exact U.property | exact q.property | exact S.property | exact ordinal_toZFSet_mem_L κ | exact ordinal_toZFSet_mem_L η | exact (ordinalBound κ).property | exact hAs | exact hLookup | exact empty_mem_L | exact ordinal_toZFSet_mem_L Ordinal.omega0 | exact natCode_mem_L 1 | exact natCode_mem_L 2 | exact natCode_mem_L 3 | exact natCode_mem_L 4 | exact natCode_mem_L 5 | exact natCode_mem_L 6 | exact natCode_mem_L k | exact orderedPair_mem_L (natCode_mem_L k) (ordinal_toZFSet_mem_L η) | exact hF | exact hUU | exact hUUU | exact hNS | exact hDS | exact hN | exact hD | exact hCross | exact hP | exact hAtom | exact hQuant | exact hSquare | exact hTriples | exact hImp | exact hChildren | exact hTruth

noncomputable def canonicalContext (κ η : Ordinal.{u}) (k : Nat) (U q S : LCarrier.{u}) :
    Tuple LCarrier.{u} 34 :=
  fun i => ⟨canonicalRaw κ η k U.val q.val S.val i,canonicalRaw_mem_L κ η k U q S i⟩

theorem canonicalContext_checks (κ η : Ordinal.{u}) (hηκ : η ≤ κ) (k : Nat)
    (U q S : LCarrier.{u})
    (hS : S.val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet q.val) :
    Checks (canonicalContext κ η k U q S) := by
  let p := canonicalContext κ η k U q S
  let c := ordinalIndexCode (η := η)
  let M := PredecessorGraph.interpretation k U.val c κ.toZFSet q.val
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · have hp : (fun i => p (syntaxMap i)) =
        snoc (UniformSyntaxSource.parameters (ordinalBound κ) (ordinalCarrier η) k) (p 18) := by
      funext i; fin_cases i <;> rfl
    change FOFormula.Satisfies lCarrierMem UniformSyntaxSource.formula (fun i => p (syntaxMap i))
    rw [hp,satisfies_ordinal_formula κ η hηκ k]
    rfl
  · have hp : (fun i => (p (relationMap i)).val) =
        ![q.val,natCode k,η.toZFSet,U.val,κ.toZFSet,
          (p 19).val,(p 20).val,(p 21).val,(p 22).val,(p 23).val,(p 24).val] := by
      funext i; fin_cases i <;> rfl
    change Satisfies ZFMem PredecessorGraph.relationCertificate (fun i => (p (relationMap i)).val)
    rw [hp,← ordinal_range η,PredecessorGraph.relationCertificate_canonical]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · apply (StructuralDiagramCertificate.satisfies_iff_canonical U.val c
      (fun i => (p (structuralMap i)).val) ⟨rfl,rfl,rfl,rfl,rfl⟩).mpr
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · have hp : (fun i => (p (atomicMap i)).val) =
        snoc (snoc (AtomicTruthFormula.parameters c M) (atomSet (k := k) U.val c))
          (trueAtomSet c M) := by
      funext i
      fin_cases i <;> first | exact (ordinal_range η).symm | rfl
    change Satisfies ZFMem AtomicTruthFormula.certificate (fun i => (p (atomicMap i)).val)
    rw [hp,AtomicTruthFormula.satisfies_certificate ordinalIndexCode_injective M (fun _ _ => Iff.rfl)]
  · have hp : (fun i => (p (solutionMap i)).val) = BoundedEvaluation.parameters (diagram c M) S.val := by
      funext i; fin_cases i <;> rfl
    change Satisfies ZFMem solutionFormula (fun i => (p (solutionMap i)).val)
    rw [hp,satisfies_solutionFormula,isSolution_iff_eq_satisfactionSet ordinalIndexCode_injective M]
    exact hS

end OneYTruth.GraphStepMatrix

