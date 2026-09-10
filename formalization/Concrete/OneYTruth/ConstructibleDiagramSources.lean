import OneYTruth.ConstructibleSyntaxCodes

/-!
# Actual constructibility of the five structural satisfaction diagrams

The complete syntax and assignment source sets have already been constructed.
Each diagram here is an identified bounded filter on a real constructible
product. Atomic truth is the only interpretation-dependent source left.
-/

namespace OneYTruth.ConstructibleDiagramSources

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel FormulaCode InternalNodes InternalProducts
open ConstructibleBoundedIteration ConstructibleSyntaxStages ConstructibleAssignmentCodes
open SyntaxDiagram

universe u v

theorem filtered_range_mem_L {p : Nat} {T : Type v} [Small.{u} T]
    (φ : Delta0Formula (p + 1)) (params : Tuple LCarrier.{u} p)
    (code : T → ZFSet.{u}) (P : T → Prop) (hsource : ZFSet.range code ∈ L)
    (hreal : ∀ a, Satisfies ZFMem φ (snoc (fun i => (params i).val) (code a)) ↔ P a) :
    ZFSet.range (fun a : {a : T // P a} => code a.val) ∈ L := by
  have hsep := deltaSep_mem_L φ params ⟨ZFSet.range code, hsource⟩
  have heq : deltaSep φ (fun i => (params i).val) (ZFSet.range code) =
      ZFSet.range (fun a : {a : T // P a} => code a.val) := by
    apply ZFSet.ext
    intro z
    rw [deltaSep, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, hφ⟩
      obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
      exact ZFSet.mem_range.mpr ⟨⟨a, (hreal a).mp hφ⟩, rfl⟩
    · intro hz
      obtain ⟨⟨a, ha⟩, rfl⟩ := ZFSet.mem_range.mp hz
      exact ⟨ZFSet.mem_range_self a, (hreal a).mpr ha⟩
  rwa [heq] at hsep

theorem pairProduct_eq_F2 (A B : ZFSet.{u}) : pairProduct A B = F2 A B := by
  apply ZFSet.ext
  intro p
  rw [pairProduct, ZFSet.mem_range, mem_F2_iff]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    exact ⟨a.val, a.property, b.val, b.property, h.symm⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), h.symm⟩

theorem pairProduct_mem_L {A B : ZFSet.{u}} (hA : A ∈ L) (hB : B ∈ L) :
    pairProduct A B ∈ L := by
  rw [pairProduct_eq_F2]
  exact op_mem_L (i := 2) hA hB

theorem scopedPairs_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hU : U ∈ L)
    (hA : ZFSet.range indexCode ∈ L) : scopedPairs (k := k) U indexCode ∈ L := by
  have hsource : ZFSet.range (crossCode (k := k) (U := U) indexCode) ∈ L := by
    rw [crossCode_range]
    exact pairProduct_mem_L (syntaxCodes_mem_L hA) (assignmentCodes_mem_L hU)
  rw [scopedPairs_eq_filtered_crossCode]
  apply filtered_range_mem_L matchingArityFormula ![]
    (crossCode (k := k) (U := U) indexCode) (fun z => z.1.1 = z.2.1) hsource
  intro z
  have ht : snoc (fun i => (![] : Tuple LCarrier.{u} 0) i |>.val) (crossCode indexCode z) =
      ![crossCode indexCode z] := by funext i; fin_cases i; rfl
  rw [ht]
  exact satisfies_matchingArityFormula indexCode z

theorem atomSet_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hnodes : scopedPairs (k := k) U indexCode ∈ L) : atomSet (k := k) U indexCode ∈ L := by
  apply filtered_range_mem_L AtomicCodeFormula.atomicFormula ![natLCarrier 5]
    (nodeCode (k := k) (U := U) indexCode) (fun z => IsAtomic z.1.2) hnodes
  intro z
  have ht : snoc (fun i => (![natLCarrier 5] : Tuple LCarrier.{u} 1) i |>.val)
      (nodeCode indexCode z) = ![natCode 5, nodeCode indexCode z] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact AtomicCodeFormula.satisfies_atomicFormula_code indexCode z

theorem quantifiedSet_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hnodes : scopedPairs (k := k) U indexCode ∈ L) : quantifiedSet (k := k) U indexCode ∈ L := by
  rw [quantifiedSet_eq_filtered_range]
  apply filtered_range_mem_L QuantifiedCodeFormula.quantifiedFormula ![natLCarrier 6]
    (nodeCode (k := k) (U := U) indexCode) (fun z => IsQuantified z.1.2) hnodes
  intro z
  have ht : snoc (fun i => (![natLCarrier 6] : Tuple LCarrier.{u} 1) i |>.val)
      (nodeCode indexCode z) = ![natCode 6, nodeCode indexCode z] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact QuantifiedCodeFormula.satisfies_quantifiedFormula_code indexCode z

theorem implicationSet_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hnodes : scopedPairs (k := k) U indexCode ∈ L) : implicationSet (k := k) U indexCode ∈ L := by
  have hsource : ZFSet.range (ImplicationCodeFormula.tripleCode (k := k) (U := U) indexCode) ∈ L := by
    rw [ImplicationCodeFormula.tripleCode_range]
    exact pairProduct_mem_L hnodes (pairProduct_mem_L hnodes hnodes)
  rw [ImplicationCodeFormula.implicationSet_eq_filtered_triples]
  apply filtered_range_mem_L ImplicationCodeFormula.implicationFormula ![natLCarrier 5]
    (ImplicationCodeFormula.tripleCode (k := k) (U := U) indexCode)
    (ImplicationCodeFormula.Matches indexCode) hsource
  intro z
  have ht : snoc (fun i => (![natLCarrier 5] : Tuple LCarrier.{u} 1) i |>.val)
      (ImplicationCodeFormula.tripleCode indexCode z) =
      ![natCode 5, ImplicationCodeFormula.tripleCode indexCode z] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact ImplicationCodeFormula.satisfies_implicationFormula_codes indexCode z

theorem childrenSet_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hU : U ∈ L)
    (hnodes : scopedPairs (k := k) U indexCode ∈ L) : childrenSet (k := k) U indexCode ∈ L := by
  have hsource : ZFSet.range (ChildrenCodeFormula.edgeCode (k := k) (U := U) indexCode) ∈ L := by
    rw [ChildrenCodeFormula.edgeCode_range]
    exact pairProduct_mem_L hnodes hnodes
  rw [ChildrenCodeFormula.childrenSet_eq_filtered_pairs]
  apply filtered_range_mem_L ChildrenCodeFormula.childrenFormula ![natLCarrier 6, ⟨U, hU⟩]
    (ChildrenCodeFormula.edgeCode (k := k) (U := U) indexCode)
    (ChildrenCodeFormula.Matches indexCode) hsource
  intro z
  have ht : snoc (fun i => (![natLCarrier 6, ⟨U, hU⟩] : Tuple LCarrier.{u} 2) i |>.val)
      (ChildrenCodeFormula.edgeCode indexCode z) =
      ![natCode 6, U, ChildrenCodeFormula.edgeCode indexCode z] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact ChildrenCodeFormula.satisfies_childrenFormula_codes indexCode z

end OneYTruth.ConstructibleDiagramSources
