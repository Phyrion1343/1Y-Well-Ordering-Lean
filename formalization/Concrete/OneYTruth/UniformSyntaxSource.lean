import OneYTruth.UniformUnionFormula
import OneYTruth.ConstructibleSyntaxCodes

/-!
# Uniform pure syntax-set definition at all bounded ordinal stages

For a fixed outer ordinal bound, one constructible code universe bounds all
finite blocks and all smaller named alphabets. The actual grammar is still
checked with the current block and alphabet; the bound adds no formulas.
-/

namespace OneYTruth.UniformSyntaxSource

open FirstOrder FirstOrder.Language Constructible Constructible.Model
open FormulaCode SyntaxDiagram InternalNodes ConstructibleCodeUniverse
open ConstructibleSyntaxStages ConstructibleBoundedIteration SyntaxGrammar

universe u v

theorem allStages_eq_of_bounds {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B A : LCarrier.{u})
    (hA : A.val = ZFSet.range indexCode)
    (hraw : ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), formulaCode indexCode φ ∈ B.val)
    (hpacked : ∀ φ : Packed k I, packedCode indexCode φ ∈ B.val) :
    (allStages B A k).val = syntaxCodes (k := k) indexCode := by
  have hi : ∀ i, indexCode i ∈ A.val := fun i => hA ▸ ZFSet.mem_range_self i
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨m,hm⟩ := (mem_allStages_iff B A k p).mp hp
    exact ZFSet.mem_range.mpr (stages_sound B A hA m p hm)
  · intro hp
    obtain ⟨⟨n,φ⟩,rfl⟩ := ZFSet.mem_range.mp hp
    exact (mem_allStages_iff B A k _).mpr
      ⟨formulaDepth φ + 1, stages_complete B A hi hraw hpacked _ φ (Nat.lt_succ_self _)⟩

def formula : FOFormula 14 :=
  UniformUnionFormula.graph (uniformFiniteIterationFormula (filterGraph ruleFormula 0).toFO)

noncomputable def parameters (B A : LCarrier.{u}) (k : Nat) : Tuple LCarrier.{u} 13 :=
  snoc (snoc (ConstructibleSyntaxStages.params B A k) emptyLCarrier) omegaLCarrier

theorem satisfies_formula {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B A S : LCarrier.{u})
    (hA : A.val = ZFSet.range indexCode)
    (hraw : ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), formulaCode indexCode φ ∈ B.val)
    (hpacked : ∀ φ : Packed k I, packedCode indexCode φ ∈ B.val) :
    FOFormula.Satisfies lCarrierMem formula (snoc (parameters B A k) S) ↔
      S.val = syntaxCodes (k := k) indexCode := by
  change FOFormula.Satisfies lCarrierMem (UniformUnionFormula.graph (grammarFamily B A k).formula)
    (snoc (snoc (grammarFamily B A k).params omegaLCarrier) S) ↔ _
  rw [UniformUnionFormula.satisfies_graph_family]
  have he := allStages_eq_of_bounds B A hA hraw hpacked
  constructor
  · intro h
    exact (congrArg (fun x : LCarrier.{u} => x.val) h).trans he
  · intro h
    exact Subtype.ext (h.trans he.symm)

noncomputable def ordinalCarrier (η : Ordinal.{u}) : LCarrier.{u} :=
  ⟨η.toZFSet, ordinal_toZFSet_mem_L η⟩

theorem ordinal_range (η : Ordinal.{u}) :
    ZFSet.range (ordinalIndexCode (η := η)) = η.toZFSet := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨⟨ξ,hξ⟩,rfl⟩
    exact ⟨ξ,hξ,rfl⟩
  · rintro ⟨ξ,hξ,rfl⟩
    exact ⟨⟨ξ,hξ⟩,rfl⟩

noncomputable def ordinalBound (κ : Ordinal.{u}) : LCarrier.{u} := codeUniverse (ordinalCarrier κ)

theorem satisfies_ordinal_formula (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (S : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem formula
      (snoc (parameters (ordinalBound κ) (ordinalCarrier η) k) S) ↔
      S.val = syntaxCodes (k := k) (ordinalIndexCode (η := η)) := by
  have hi : ∀ i : {ξ : Ordinal.{u} // ξ < η}, ordinalIndexCode i ∈ (ordinalCarrier κ).val :=
    fun i => Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_of_lt_of_le i.property hη)
  apply satisfies_formula
  · exact (ordinal_range η).symm
  · intro n φ
    exact rawCode_mem hi (toRaw φ)
  · intro φ
    exact pair_mem (natCode_mem (ordinalCarrier κ) φ.1) (rawCode_mem hi (toRaw φ.2))

end OneYTruth.UniformSyntaxSource
