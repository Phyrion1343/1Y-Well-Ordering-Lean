import OneYTruth.InternalRecursionEnvironment

/-! # Formula-defined predecessor restrictions in a weak internal carrier

Only the displayed pure FO Separation and transitivity are used. The
selected object is an actual member of the carrier, with exact raw semantics.
-/

namespace OneYTruth.ExternalTower.RecursionEnvironment

open Constructible Constructible.Model

universe u

noncomputable section
variable {V : ZFSet.{u}} (E : RecursionEnvironment V)
include E
@[simp]
theorem satisfies_restrictionMember_carrier
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple (ZFCarrier V) n)
    (top pair : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V)
        (formulaRestrictionMemberFormula classFormula relationFormula)
        (snoc (snoc params top) pair) ↔
      ∃ input output : ZFCarrier V,
        pair.1 = ZFSet.pair input.1 output.1 ∧
          FOFormula.Satisfies (zfCarrierMem V) classFormula
            (snoc params input) ∧
          FOFormula.Satisfies (zfCarrierMem V) relationFormula
            (snoc (snoc params input) top) := by
  simp only [formulaRestrictionMemberFormula, FOFormula.Satisfies]
  apply exists_congr
  intro input
  apply exists_congr
  intro output
  rw [Delta0Formula.satisfies_toFO, Delta0Formula.satisfies_absolute E.transitive,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  let full := snoc (snoc (snoc (snoc params top) pair) input) output
  have hpair : full ((Fin.last (n + 1)).castSucc.castSucc) = pair := by
    simp only [full, snoc_castSucc, snoc_last]
  have hinput : full ((Fin.last (n + 2)).castSucc) = input := by
    simp only [full, snoc_castSucc, snoc_last]
  have houtput : full (Fin.last (n + 3)) = output := by
    simp only [full, snoc_last]
  rw [show
    snoc (snoc (snoc (snoc params top) pair) input) output = full by rfl]
  dsimp only [Delta0Formula.val]
  rw [hpair, hinput, houtput]
  rw [satisfies_classFormulaAt_generic,
    satisfies_relationFormulaAt_generic]
  have hparams :
      (fun i =>
        full
          (i.castSucc.castSucc.castSucc.castSucc)) = params := by
    funext i
    simp only [full, snoc_castSucc]
  have htop :
      full
          ((Fin.last n).castSucc.castSucc.castSucc) = top := by
    simp only [full, snoc_castSucc, snoc_last]
  rw [hparams, hinput, htop]

/-! ## The represented restriction -/

/-- Separation of a constructible graph by the formula-defined predecessor
condition. -/
def formulaRestrictionCarrier {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple (ZFCarrier V) n)
    (graph top : ZFCarrier V) : ZFCarrier V :=
  Classical.choose (E.separation (n + 1)
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph)

@[simp]
theorem mem_formulaRestrictionCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple (ZFCarrier V) n)
    (graph top pair : ZFCarrier V) :
    pair.1 ∈ (formulaRestrictionCarrier E
      classFormula relationFormula params graph top).1 ↔
      pair.1 ∈ graph.1 ∧
        ∃ input output : ZFCarrier V,
          pair.1 = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies (zfCarrierMem V) classFormula
              (snoc params input) ∧
            FOFormula.Satisfies (zfCarrierMem V) relationFormula
              (snoc (snoc params input) top) := by
  rw [formulaRestrictionCarrier]
  rw [Classical.choose_spec (E.separation (n + 1)
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph) pair]
  rw [satisfies_restrictionMember_carrier E]

/-- Raw membership form of the same restriction specification. -/
theorem mem_formulaRestrictionCarrier_raw_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple (ZFCarrier V) n)
    (graph top : ZFCarrier V) (pair : ZFSet.{u}) :
    pair ∈ (formulaRestrictionCarrier E
      classFormula relationFormula params graph top).1 ↔
      pair ∈ graph.1 ∧
        ∃ input output : ZFCarrier V,
          pair = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies (zfCarrierMem V) classFormula
              (snoc params input) ∧
            FOFormula.Satisfies (zfCarrierMem V) relationFormula
              (snoc (snoc params input) top) := by
  constructor
  · intro hpair
    let pairL : ZFCarrier V :=
      ⟨pair, E.transitive.mem_trans hpair
        (formulaRestrictionCarrier E
          classFormula relationFormula params graph top).2⟩
    exact (mem_formulaRestrictionCarrier_iff E
      classFormula relationFormula params graph top pairL).mp hpair
  · rintro ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩
    have hpairL : pair ∈ V := E.transitive.mem_trans hpairGraph graph.2
    let pairL : ZFCarrier V := ⟨pair, hpairL⟩
    apply (mem_formulaRestrictionCarrier_iff E
      classFormula relationFormula params graph top pairL).mpr
    exact ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩


end
end OneYTruth.ExternalTower.RecursionEnvironment



