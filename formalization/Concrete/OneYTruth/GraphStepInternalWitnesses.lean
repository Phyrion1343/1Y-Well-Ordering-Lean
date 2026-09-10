import OneYTruth.InternalGraphInput
import OneYTruth.GraphStepSigmaSoundness
import OneYTruth.InternalSyntaxCodes
import OneYTruth.SatisfactionTrace

/-! All eighteen structural witnesses of the whole-step certificate actually
belong to a schema-closed smaller domain; the grammar histories are supplied
by the already proved internal complete-iteration theorem. -/

namespace OneYTruth.GraphStepSigma

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open InternalClosure InternalProducts InternalNodes SyntaxDiagram FormulaCode
open UniformSyntaxSource GraphStepMatrix AtomicRelationGraphs AssignmentLookup

universe u v

theorem canonicalRaw_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (κ η : Ordinal.{u}) (k : Nat) (U q S : ZFSet.{u})
    (hU : U ∈ V) (hκ : κ.toZFSet ∈ V) (hη : η.toZFSet ∈ V)
    (hB : (ordinalBound κ).val ∈ V) (hq : q ∈ V) (hS : S ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V)
    (hAssignments : assignmentCodes U ∈ V) (hLookup : lookupSet U ∈ V) :
    ∀ i, canonicalRaw κ η k U q S i ∈ V := by
  have hnat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n,rfl⟩) hOmega
  have hempty : (∅ : ZFSet.{u}) ∈ V := by simpa [natCode] using hnat 0
  let c := ordinalIndexCode (η := η)
  let M := PredecessorGraph.interpretation k U c κ.toZFSet q
  have hA : ZFSet.range c ∈ V := by rw [ordinal_range]; exact hη
  have hF : syntaxCodes (k := k) c ∈ V :=
    InternalSyntaxCodes.syntaxCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
      (ordinalCarrier η) (ordinal_range η).symm hη
  obtain ⟨hP,hAtom,hImp,hQuant,hChildren⟩ := InternalDiagram.structural_sets_mem hV N hmem
    hCol hSep hpair hUnion (hnat 5) (hnat 6) hU c hF hAssignments
  have hN : namedGraph c M ∈ V := InternalGraphInput.namedGraph_mem hV N hmem hCol hSep
    hpair hUnion c hU hA hq (hnat k)
  have hD : diagonalGraph M ∈ V := InternalGraphInput.diagonalGraph_mem hV N hmem hCol hSep
    hpair hUnion c hU hκ hq (hnat k)
  have hp : ∀ i, AtomicTruthFormula.parameters c M i ∈ V := by
    intro i
    fin_cases i <;> first | exact hU | exact hLookup | exact hAssignments | exact hOmega | exact hA | exact hN | exact hD | exact hnat 1 | exact hnat 2 | exact hnat 3 | exact hnat 4
  have hTruth : trueAtomSet c M ∈ V := InternalGraphInput.trueAtomSet_mem hV N hmem hSep
    ordinalIndexCode_injective M (fun _ _ => Iff.rfl) hp hAtom
  have prod {A B : ZFSet.{u}} (ha : A ∈ V) (hb : B ∈ V) : pairProduct A B ∈ V :=
    InternalGraphInput.product_mem hV N hmem hCol hSep hpair hUnion ha hb
  have hUU := prod hU hU
  have hUUU := prod hU hUU
  have hNS := prod hA hUU
  have hDS := prod (hnat k) hUUU
  have hCross := prod hF hAssignments
  have hSquare := prod hP hP
  have hTriples := prod hP hSquare
  intro i
  fin_cases i <;> first | exact hU | exact hκ | exact hB | exact hAssignments | exact hLookup | exact hOmega | exact hempty | exact hnat 1 | exact hnat 2 | exact hnat 3 | exact hnat 4 | exact hnat 5 | exact hnat 6 | exact hpair _ (hnat k) _ hη | exact hq | exact hS | exact hnat k | exact hη | exact hF | exact hUU | exact hUUU | exact hNS | exact hDS | exact hN | exact hD | exact hCross | exact hP | exact hAtom | exact hQuant | exact hSquare | exact hTriples | exact hImp | exact hChildren | exact hTruth

end OneYTruth.GraphStepSigma
