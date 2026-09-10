import OneYTruth.GraphStepMatrix

/-! Soundness of the whole-step formula, with every candidate set checked. -/

namespace OneYTruth.GraphStepMatrix

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open Constructible.Delta0Formula FormulaCode SyntaxDiagram BoundedEvaluation
open InternalNodes
open ConstructibleAssignmentCodes AssignmentLookup UniformSyntaxSource

universe u

noncomputable def fixedParameters (κ : Ordinal.{u}) (U : LCarrier.{u}) : Tuple LCarrier.{u} 13 :=
  ![U,ordinalCarrier κ,ordinalBound κ,
    ⟨assignmentCodes U.val,assignmentCodes_mem_L U.property⟩,
    ⟨lookupSet U.val,lookupSet_mem_L U.property⟩,
    omegaLCarrier,emptyLCarrier,natLCarrier 1,natLCarrier 2,natLCarrier 3,
    natLCarrier 4,natLCarrier 5,natLCarrier 6]

def BaseParameters (κ : Ordinal.{u}) (U : LCarrier.{u}) (p : Tuple LCarrier.{u} 34) : Prop :=
  p 0 = U ∧ p 1 = ordinalCarrier κ ∧ p 2 = ordinalBound κ ∧
    (p 3).val = assignmentCodes U.val ∧ (p 4).val = lookupSet U.val ∧
    p 5 = omegaLCarrier ∧ p 6 = emptyLCarrier ∧ p 7 = natLCarrier 1 ∧
    p 8 = natLCarrier 2 ∧ p 9 = natLCarrier 3 ∧ p 10 = natLCarrier 4 ∧
    p 11 = natLCarrier 5 ∧ p 12 = natLCarrier 6

theorem checks_sound (κ η : Ordinal.{u}) (hηκ : η ≤ κ) (k : Nat)
    (U : LCarrier.{u}) (p : Tuple LCarrier.{u} 34)
    (hbase : BaseParameters κ U p)
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet) (hc : Checks p) :
    (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := hbase
  obtain ⟨hpair,hsyntax,hrel,hstruct,hatomic,hsol⟩ := hc
  have hpair' := ZFSet.pair_inj.mp (hpair.symm.trans hstage)
  have h16 : p 16 = natLCarrier k := Subtype.ext hpair'.1
  have h17 : p 17 = ordinalCarrier η := Subtype.ext hpair'.2
  have hsyntaxMap : (fun i => p (syntaxMap i)) =
      snoc (UniformSyntaxSource.parameters (ordinalBound κ) (ordinalCarrier η) k) (p 18) := by
    funext i
    fin_cases i <;> first | exact h2 | exact h17 | exact h5 | exact h16 | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | rfl
  rw [hsyntaxMap, satisfies_ordinal_formula κ η hηκ k (p 18)] at hsyntax
  have h0v := congrArg (fun x : LCarrier.{u} => x.val) h0
  have h1v := congrArg (fun x : LCarrier.{u} => x.val) h1
  have h5v := congrArg (fun x : LCarrier.{u} => x.val) h5
  have h7v := congrArg (fun x : LCarrier.{u} => x.val) h7
  have h8v := congrArg (fun x : LCarrier.{u} => x.val) h8
  have h9v := congrArg (fun x : LCarrier.{u} => x.val) h9
  have h10v := congrArg (fun x : LCarrier.{u} => x.val) h10
  have h11v := congrArg (fun x : LCarrier.{u} => x.val) h11
  have h12v := congrArg (fun x : LCarrier.{u} => x.val) h12
  have h16v := congrArg (fun x : LCarrier.{u} => x.val) h16
  have h17v : (p 17).val = ZFSet.range (ordinalIndexCode (η := η)) :=
    (congrArg (fun x : LCarrier.{u} => x.val) h17).trans (ordinal_range η).symm
  let M := PredecessorGraph.interpretation k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val
  have hrelationMap : (fun i => (p (relationMap i)).val) =
      ![(p 14).val,natCode k,ZFSet.range (ordinalIndexCode (η := η)),U.val,κ.toZFSet,
        (p 19).val,(p 20).val,(p 21).val,(p 22).val,(p 23).val,(p 24).val] := by
    funext i
    fin_cases i <;> first | exact h0v | exact h1v | exact h16v | exact h17v | rfl
  rw [hrelationMap, PredecessorGraph.relationCertificate_canonical] at hrel
  obtain ⟨_,_,_,_,hN,hD⟩ := hrel
  have hsp : StructuralDiagramCertificate.SourceParameters (k := k) U.val
      (ordinalIndexCode (η := η)) (fun i => (p (structuralMap i)).val) :=
    ⟨h0v,hsyntax,h3,h11v,h12v⟩
  have hcanonical := (StructuralDiagramCertificate.satisfies_iff_canonical U.val
    (ordinalIndexCode (η := η)) _ hsp).mp hstruct
  obtain ⟨_,hnodes,hatoms,hquant,_,_,himp,hchildren⟩ := hcanonical
  have hatomicMap : (fun i => (p (atomicMap i)).val) =
      snoc (snoc (AtomicTruthFormula.parameters (ordinalIndexCode (η := η)) M)
        (atomSet (k := k) U.val (ordinalIndexCode (η := η)))) (p 33).val := by
    funext i
    fin_cases i <;> first | exact h0v | exact h3 | exact h4 | exact h5v | exact h17v | exact hN | exact hD | exact h7v | exact h8v | exact h9v | exact h10v | exact hatoms | rfl
  rw [hatomicMap, AtomicTruthFormula.satisfies_certificate ordinalIndexCode_injective M
    (fun _ _ => Iff.rfl)] at hatomic
  have hsolutionMap : (fun i => (p (solutionMap i)).val) =
      BoundedEvaluation.parameters (diagram (ordinalIndexCode (η := η)) M) (p 15).val := by
    funext i
    fin_cases i <;> first | exact hnodes | exact hatoms | exact hatomic | exact himp | exact hquant | exact hchildren | rfl
  rw [hsolutionMap, satisfies_solutionFormula, isSolution_iff_eq_satisfactionSet
    ordinalIndexCode_injective M] at hsol
  exact hsol

end OneYTruth.GraphStepMatrix


