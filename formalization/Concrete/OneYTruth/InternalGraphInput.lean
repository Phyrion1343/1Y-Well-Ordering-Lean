import OneYTruth.GraphRelationCertificate
import OneYTruth.AtomicTruthCertificate
import OneYTruth.InternalSatisfactionSources
import OneYTruth.InternalBoundedIteration

/-! Actual predecessor relations, atomic truth, and local satisfaction inside
a transitive domain.  Only the complete syntax, assignment, and lookup sources
are inputs; no atomic-table or satisfaction-set membership is postulated. -/

namespace OneYTruth.InternalGraphInput

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open InternalClosure InternalProducts AtomicRelationGraphs SyntaxDiagram
open InternalNodes AssignmentLookup PredecessorGraph

universe u v w

section

variable {K : Nat} {J : Type w} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)

include hV N hmem hSep in
theorem sep_mem {p : Nat} (φ : Delta0Formula (p+1)) (params : Tuple ZFSet.{u} p)
    (hp : ∀ i, params i ∈ V) {B : ZFSet.{u}} (hB : B ∈ V) :
    ZFSet.sep (fun x => Satisfies ZFMem φ (snoc params x)) B ∈ V := by
  exact InternalBoundedIteration.deltaSep_mem hV N hmem hSep φ
    (fun i => ⟨params i,hp i⟩) hB

include hV N hmem hCol hSep hpair hUnion in
theorem product_mem {A B : ZFSet.{u}} (hA : A ∈ V) (hB : B ∈ V) :
    pairProduct A B ∈ V := by
  have hr := hasReplacement_of_collection_separation N hmem hCol hSep
  exact pairProduct_mem hV N hmem (hr 1 (pairFormula K J))
    (hr 1 (mixedSliceGraphFormula K J)) hpair hUnion hA hB

include hV N hmem hCol hSep hpair hUnion

theorem namedGraph_mem {k : Nat} {I : Type v} [Small.{u} I]
    {U κ q : ZFSet.{u}} (c : I → ZFSet.{u})
    (hU : U ∈ V) (hA : ZFSet.range c ∈ V) (hq : q ∈ V)
    (hk : (natCode k : ZFSet.{u}) ∈ V) :
    namedGraph c (interpretation k U c κ q) ∈ V := by
  rw [namedGraph_eq_sep]
  apply sep_mem hV N hmem hSep namedFormula ![q,natCode k,ZFSet.range c,U]
  · intro i
    fin_cases i <;> assumption
  · exact product_mem hV N hmem hCol hSep hpair hUnion hA
      (product_mem hV N hmem hCol hSep hpair hUnion hU hU)

theorem diagonalGraph_mem {k : Nat} {I : Type v}
    {U κ q : ZFSet.{u}} (c : I → ZFSet.{u})
    (hU : U ∈ V) (hκ : κ ∈ V) (hq : q ∈ V)
    (hk : (natCode k : ZFSet.{u}) ∈ V) :
    diagonalGraph (interpretation k U c κ q) ∈ V := by
  rw [diagonalGraph_eq_sep]
  apply sep_mem hV N hmem hSep diagonalFormula ![q,κ,natCode k,U]
  · intro i
    fin_cases i <;> assumption
  · exact product_mem hV N hmem hCol hSep hpair hUnion hk
      (product_mem hV N hmem hCol hSep hpair hUnion hU
        (product_mem hV N hmem hCol hSep hpair hUnion hU hU))

omit hCol hpair hUnion in
theorem trueAtomSet_mem {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {c : I → ZFSet.{u}} (hi : Function.Injective c)
    (M : Interpretation k I (ZFCarrier U))
    (hm : ∀ x y, M.mem x y ↔ x.val ∈ y.val)
    (hparams : ∀ i, AtomicTruthFormula.parameters c M i ∈ V)
    (hAtoms : atomSet (k := k) U c ∈ V) : trueAtomSet c M ∈ V := by
  rw [AtomicTruthFormula.trueAtomSet_eq_sep hi M hm]
  exact sep_mem hV N hmem hSep AtomicTruthFormula.formula _ hparams hAtoms

theorem step_mem_of_sources {k : Nat} {I : Type v} [Small.{u} I]
    {U κ q : ZFSet.{u}} {c : I → ZFSet.{u}} (hi : Function.Injective c)
    (hU : U ∈ V) (hκ : κ ∈ V) (hq : q ∈ V) (hA : ZFSet.range c ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V)
    (hSyntax : syntaxCodes (k := k) c ∈ V)
    (hAssignments : assignmentCodes U ∈ V) (hLookup : lookupSet U ∈ V) :
    PredecessorGraph.step k U c κ q ∈ V := by
  have hnat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n,rfl⟩) hOmega
  have hempty : (∅ : ZFSet.{u}) ∈ V := by simpa [natCode] using hnat 0
  let M := interpretation k U c κ q
  have hN : namedGraph c M ∈ V := namedGraph_mem hV N hmem hCol hSep hpair hUnion c hU hA hq (hnat k)
  have hD : diagonalGraph M ∈ V := diagonalGraph_mem hV N hmem hCol hSep hpair hUnion c hU hκ hq (hnat k)
  have hstruct := InternalDiagram.structural_sets_mem hV N hmem hCol hSep hpair hUnion
    (hnat 5) (hnat 6) hU c hSyntax hAssignments
  have hp : ∀ i, AtomicTruthFormula.parameters c M i ∈ V := by
    intro i
    fin_cases i <;> first | exact hU | exact hLookup | exact hAssignments | exact hOmega | exact hA | exact hN | exact hD | exact hnat 1 | exact hnat 2 | exact hnat 3 | exact hnat 4
  have ht : trueAtomSet c M ∈ V := trueAtomSet_mem hV N hmem hSep hi M (fun _ _ => Iff.rfl) hp hstruct.2.1
  exact satisfactionSet_mem_of_internal_sources hV N hmem hCol hSep hpair hUnion
    hOmega hempty (hnat 5) (hnat 6) hU hi hSyntax hAssignments M ht

end
end OneYTruth.InternalGraphInput
