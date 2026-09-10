import OneYTruth.ConstructibleEventualTruth

/-!
# Actual constructibility of full fixed-domain satisfaction

The two complete source sets and all five structural diagrams are supplied
by their proved constructions. A real pure formula separates eventual
truth from the nodes. Only the actual atomic interpretation table remains
an interpretation-dependent constructibility hypothesis.
-/

namespace OneYTruth.ConstructibleDiagramSources

open Constructible Constructible.Model
open FormulaCode SyntaxDiagram BoundedEvaluation ConstructibleEvaluationFamily

universe u v

theorem filtered_range_FO_mem_L {p : Nat} {T : Type v} [Small.{u} T]
    (φ : FOFormula (p + 1)) (params : Tuple LCarrier.{u} p)
    (code : T → ZFSet.{u}) (P : T → Prop) (hsource : ZFSet.range code ∈ L)
    (hreal : ∀ a (ha : code a ∈ L),
      FOFormula.Satisfies lCarrierMem φ (snoc params ⟨code a, ha⟩) ↔ P a) :
    ZFSet.range (fun a : {a : T // P a} => code a.val) ∈ L := by
  obtain ⟨S, hS⟩ := exists_separationLCarrier φ params ⟨ZFSet.range code, hsource⟩
  have heq : S.val = ZFSet.range (fun a : {a : T // P a} => code a.val) := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz S.property⟩
      obtain ⟨hzsource, hzφ⟩ := (hS zL).mp hz
      obtain ⟨a, ha⟩ := ZFSet.mem_range.mp hzsource
      have hca : code a ∈ L := ha.symm ▸ zL.property
      have he : zL = (⟨code a, hca⟩ : LCarrier.{u}) := Subtype.ext ha.symm
      rw [he] at hzφ
      exact ZFSet.mem_range.mpr ⟨⟨a, (hreal a hca).mp hzφ⟩, ha⟩
    · intro hz
      obtain ⟨⟨a, hPa⟩, rfl⟩ := ZFSet.mem_range.mp hz
      have haL : code a ∈ L := mem_L_of_mem (ZFSet.mem_range_self a) hsource
      exact (hS ⟨code a, haL⟩).mpr ⟨ZFSet.mem_range_self a, (hreal a haL).mpr hPa⟩
  rw [← heq]
  exact S.property

theorem diagram_hasConstructibleFields {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) (hU : U ∈ L)
    (hA : ZFSet.range indexCode ∈ L) (hAtoms : trueAtomSet indexCode M ∈ L) :
    HasConstructibleFields (diagram indexCode M) := by
  have hnodes := scopedPairs_mem_L (k := k) hU hA
  exact ⟨hnodes, atomSet_mem_L hnodes, hAtoms, implicationSet_mem_L hnodes,
    quantifiedSet_mem_L hnodes, childrenSet_mem_L hU hnodes⟩

theorem satisfactionSet_mem_L_of_atomic_table {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (hU : U ∈ L)
    (hA : ZFSet.range indexCode ∈ L) (hAtoms : trueAtomSet indexCode M ∈ L) :
    satisfactionSet indexCode M ∈ L := by
  let D := diagram indexCode M
  have hD : HasConstructibleFields D := diagram_hasConstructibleFields M hU hA hAtoms
  rw [satisfactionSet_eq_filtered_nodes]
  apply filtered_range_FO_mem_L ConstructibleEvaluationFamily.eventualFormula
    (snoc (ConstructibleEvaluationFamily.family D hD).params omegaLCarrier)
    (nodeCode (k := k) (U := U) indexCode)
    (fun z => OneYTruth.realize M z.1.2 Empty.elim z.2) hD.1
  intro z hz
  rw [ConstructibleEvaluationFamily.satisfies_eventualFormula]
  constructor
  · rintro ⟨m, hm⟩
    have hvalue := hm (max m (formulaDepth z.1.2 + 1)) (Nat.le_max_left _ _)
    exact (node_mem_iterate_iff_of_depth hi M z.1.2 z.2 _ (Nat.le_max_right _ _)).mp hvalue
  · intro htruth
    refine ⟨formulaDepth z.1.2 + 1, ?_⟩
    intro n hn
    exact (node_mem_iterate_iff_of_depth hi M z.1.2 z.2 n hn).mpr htruth

end OneYTruth.ConstructibleDiagramSources
