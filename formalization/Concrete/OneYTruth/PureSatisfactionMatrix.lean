import OneYTruth.AtomicTruthCertificate
import OneYTruth.StructuralDiagramCertificate
import OneYTruth.NaturalTagCertificate

/-! The complete bounded Tarski check for the pure membership language.
All auxiliary structural sets and constructor tags are checked. -/

namespace OneYTruth.PureSatisfactionMatrix

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language FormulaCode InternalNodes SyntaxDiagram
open AtomicRelationGraphs AssignmentLookup BoundedEvaluation

universe u v

def interpretation (U : ZFSet.{u}) : Interpretation 0 Empty (ZFCarrier U) where
  mem := zfCarrierMem U
  named := fun i => i.elim
  diagonal := fun i => Fin.elim0 i

theorem empty_range : ZFSet.range (Empty.elim : Empty → ZFSet.{u}) = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_range, ZFSet.notMem_empty, iff_false]
  rintro ⟨i, _⟩
  exact i.elim

theorem namedGraph_eq_empty (U : ZFSet.{u}) :
    namedGraph (Empty.elim : Empty → ZFSet.{u}) (interpretation U) = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [namedGraph, ZFSet.mem_range, ZFSet.notMem_empty, iff_false]
  rintro ⟨i, _⟩
  exact i.val.1.elim

theorem diagonalGraph_eq_empty (U : ZFSet.{u}) :
    diagonalGraph (interpretation U) = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [diagonalGraph, ZFSet.mem_range, ZFSet.notMem_empty, iff_false]
  rintro ⟨i, _⟩
  exact Fin.elim0 i.val.1

/-- U, omega, zero, Sat; tags 1..6; syntax, assignments, lookup;
cross, nodes, atoms, quantified, square, triples, implications, children, true atoms. -/
def tagMap : Fin 12 → Fin 22 := ![0,1,2,0,0,4,5,6,7,8,9,0]
def structuralMap : Fin 13 → Fin 22 := ![0,10,11,8,9,13,14,15,16,17,18,19,20]
def atomicMap : Fin 13 → Fin 22 := ![0,12,11,1,2,2,2,4,5,6,7,15,21]
def solutionMap : Fin 7 → Fin 22 := ![3,14,15,21,19,16,20]

def matrix : Delta0Formula 22 :=
  .conj (NaturalTagCertificate.sixTags.rename tagMap)
    (.conj (StructuralDiagramCertificate.formula.rename structuralMap)
      (.conj (AtomicTruthFormula.certificate.rename atomicMap)
        (solutionFormula.rename solutionMap)))

def Checks (p : Fin 22 → ZFSet.{u}) : Prop :=
  Satisfies ZFMem NaturalTagCertificate.sixTags (p ∘ tagMap) ∧
    Satisfies ZFMem StructuralDiagramCertificate.formula (p ∘ structuralMap) ∧
    Satisfies ZFMem AtomicTruthFormula.certificate (p ∘ atomicMap) ∧
    Satisfies ZFMem solutionFormula (p ∘ solutionMap)

theorem satisfies_matrix (p : Fin 22 → ZFSet.{u}) :
    Satisfies ZFMem matrix p ↔ Checks p := by
  simp only [matrix, Satisfies, Delta0Formula.satisfies_rename, Checks, Function.comp_def]

attribute [irreducible] matrix

theorem checks_sound (p : Fin 22 → ZFSet.{u})
    (hOmega : p 1 = Ordinal.omega0.toZFSet) (hZero : p 2 = ∅)
    (hF : p 10 = syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}))
    (hA : p 11 = assignmentCodes (p 0)) (hLookup : p 12 = lookupSet (p 0))
    (h : Checks p) :
    p 14 = scopedPairs (k := 0) (p 0) (Empty.elim : Empty → ZFSet.{u}) ∧
      p 3 = satisfactionSet Empty.elim (interpretation (p 0)) := by
  obtain ⟨ht, hs, ha, hsol⟩ := h
  have hi : Function.Injective (Empty.elim : Empty → ZFSet.{u}) := fun i => i.elim
  have tags := (NaturalTagCertificate.satisfies_sixTags (p ∘ tagMap) hOmega hZero).mp ht
  change p 4 = natCode 1 ∧ p 5 = natCode 2 ∧ p 6 = natCode 3 ∧
    p 7 = natCode 4 ∧ p 8 = natCode 5 ∧ p 9 = natCode 6 at tags
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := tags
  have hp : StructuralDiagramCertificate.SourceParameters (k := 0) (p 0)
      (Empty.elim : Empty → ZFSet.{u}) (p ∘ structuralMap) := ⟨rfl,hF,hA,h5,h6⟩
  have hc := (StructuralDiagramCertificate.satisfies_iff_canonical (p 0)
    (Empty.elim : Empty → ZFSet.{u}) (p ∘ structuralMap) hp).mp hs
  change p 13 = _ ∧ p 14 = _ ∧ p 15 = _ ∧ p 16 = _ ∧ p 17 = _ ∧
    p 18 = _ ∧ p 19 = _ ∧ p 20 = _ at hc
  obtain ⟨_,hn,hat,hq,_,_,himp,hchild⟩ := hc
  let M := interpretation (p 0)
  have hea : p ∘ atomicMap = snoc (snoc
      (AtomicTruthFormula.parameters (Empty.elim : Empty → ZFSet.{u}) M)
      (atomSet (k := 0) (p 0) Empty.elim)) (p 21) := by
    funext i
    fin_cases i <;> simp [atomicMap, Function.comp_def, constructible_snoc_eq,
      Fin.snoc, Fin.castLT, AtomicTruthFormula.parameters, M, hOmega, hZero,
      hA, hLookup, h1,h2,h3,h4,hat, empty_range, namedGraph_eq_empty, diagonalGraph_eq_empty]
  rw [hea, AtomicTruthFormula.satisfies_certificate hi M (fun _ _ => Iff.rfl)] at ha
  have heq : p ∘ solutionMap = parameters (diagram Empty.elim M) (p 3) := by
    funext i
    fin_cases i <;> first | exact hn | exact hat | exact ha | exact himp | exact hq | exact hchild | rfl
  rw [heq, satisfies_solutionFormula, isSolution_iff_eq_satisfactionSet hi M] at hsol
  exact ⟨hn,hsol⟩

noncomputable def actual (U : ZFSet.{u}) : Fin 22 → ZFSet.{u} :=
  let F := syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u})
  let A := assignmentCodes U
  let nodes := scopedPairs (k := 0) U (Empty.elim : Empty → ZFSet.{u})
  ![U,Ordinal.omega0.toZFSet,∅,satisfactionSet Empty.elim (interpretation U),
    natCode 1,natCode 2,natCode 3,natCode 4,natCode 5,natCode 6,
    F,A,lookupSet U,InternalProducts.pairProduct F A,nodes,
    atomSet (k := 0) U Empty.elim,quantifiedSet (k := 0) U Empty.elim,
    InternalProducts.pairProduct nodes nodes,
    InternalProducts.pairProduct nodes (InternalProducts.pairProduct nodes nodes),
    implicationSet (k := 0) U Empty.elim,childrenSet (k := 0) U Empty.elim,
    trueAtomSet Empty.elim (interpretation U)]

theorem actual_checks (U : ZFSet.{u}) : Checks (actual U) := by
  have hi : Function.Injective (Empty.elim : Empty → ZFSet.{u}) := fun i => i.elim
  refine ⟨?_,?_,?_,?_⟩
  · exact (NaturalTagCertificate.satisfies_sixTags _ rfl rfl).mpr ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (StructuralDiagramCertificate.satisfies_iff_canonical U
      (Empty.elim : Empty → ZFSet.{u}) _ ⟨rfl,rfl,rfl,rfl,rfl⟩).mpr
        ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · have he : actual U ∘ atomicMap = snoc (snoc
        (AtomicTruthFormula.parameters (Empty.elim : Empty → ZFSet.{u}) (interpretation U))
        (atomSet (k := 0) U Empty.elim)) (trueAtomSet Empty.elim (interpretation U)) := by
      funext i
      fin_cases i <;> simp [actual,atomicMap,AtomicTruthFormula.parameters,
        constructible_snoc_eq,Fin.snoc,Fin.castLT,empty_range,namedGraph_eq_empty,diagonalGraph_eq_empty]
    rw [he,AtomicTruthFormula.satisfies_certificate hi (interpretation U) (fun _ _ => Iff.rfl)]
  · change Satisfies ZFMem solutionFormula
      (parameters (diagram Empty.elim (interpretation U)) (satisfactionSet Empty.elim (interpretation U)))
    rw [satisfies_solutionFormula,isSolution_iff_eq_satisfactionSet hi (interpretation U)]

end OneYTruth.PureSatisfactionMatrix
