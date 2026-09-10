import OneYTruth.SatisfactionTrace
import OneYTruth.UniformTruth
import OneYTruth.ConstructibleCodes
import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationBareStage

/-!
# Comparing the canonical towers on elementary nested L domains

The small tower is rebuilt on its own domain and with its own diagonal
bound. Only the earlier stages' truth traces are used to identify a
current restricted auxiliary reduct with that rebuilt interpretation.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.FiniteSequenceZF FormulaCode
open FirstOrder FirstOrder.Language

universe u v

def embedStage {α κ : Ordinal.{u}} (h : α ≤ κ) (s : Stage α) : Stage κ :=
  (s.1, ⟨s.2.val, s.2.property.trans h⟩)

noncomputable def traceBlock {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) (k : Nat) :
    Fin (k + 1) → ZFCarrier (LStageZF α) :=
  fun j => ⟨natCode j.val, natCode_mem_LStageZF_of_isSuccLimit hα j.val⟩

noncomputable def traceIndex {α : Ordinal.{u}} (s : Stage α) :
    {ξ : Ordinal.{u} // ξ < s.2.val} → ZFCarrier (LStageZF α) :=
  fun ξ => ⟨ξ.val.toZFSet, ordinalIndexCode_mem_LStageZF s.2.property ξ⟩

theorem current_reduct_eq {α κ : Ordinal.{u}} (h : α ≤ κ)
    (hα : Order.IsSuccLimit α) (s : Stage α)
    (ih : ∀ t, Earlier t s → ∀ e a : ZFCarrier (LStageZF α),
      ZFSet.pair e.val a.val ∈ truth (LStageZF α) t ↔
        ZFSet.pair e.val a.val ∈ truth (LStageZF κ) (embedStage h t)) :
    Auxiliary.reduct (Auxiliary.restrict (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF_mono h))
      (traceBlock hα s.1) (traceIndex s) = interpretation (LStageZF α) s := by
  change Interpretation.mk _ _ _ = Interpretation.mk _ _ _
  congr 1
  · funext j ξ e a
    apply propext
    change ZFSet.pair (ZFSet.pair (natCode j.val) ξ.val) (ZFSet.pair e.val a.val) ∈
      @uniformSet κ (LStageZF κ) ↔
      ∃ ζ : {ζ : Ordinal.{u} // ζ < α}, ξ.val = ζ.val.toZFSet ∧
        ZFSet.pair e.val a.val ∈ truth (LStageZF α) (j.val, ⟨ζ.val, ζ.property.le⟩)
    rw [mem_uniformSet_at_block_iff]
    constructor
    · rintro ⟨ζ, hζ, ht⟩
      have hζα : ζ.val < α :=
        MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
          (by rw [← hζ]; exact ξ.property)
      refine ⟨⟨ζ.val, hζα⟩, hζ, ?_⟩
      exact (ih (j.val, ⟨ζ.val, hζα.le⟩) (Prod.Lex.left _ _ j.isLt) e a).mpr ht
    · rintro ⟨ζ, hζ, ht⟩
      refine ⟨⟨ζ.val, ζ.property.trans_le h⟩, hζ, ?_⟩
      exact (ih (j.val, ⟨ζ.val, ζ.property.le⟩) (Prod.Lex.left _ _ j.isLt) e a).mp ht
  · funext ξ e a
    apply propext
    change ZFSet.pair (ZFSet.pair (natCode s.1) ξ.val.toZFSet) (ZFSet.pair e.val a.val) ∈
      @uniformSet κ (LStageZF κ) ↔
      ZFSet.pair e.val a.val ∈ truth (LStageZF α) (s.1, ⟨ξ.val, ξ.property.le.trans s.2.property⟩)
    rw [mem_uniformSet_at_block_iff]
    constructor
    · rintro ⟨ζ, hζ, ht⟩
      have hζξ : ζ.val = ξ.val := Ordinal.toZFSet_injective hζ.symm
      apply (ih (s.1, ⟨ξ.val, ξ.property.le.trans s.2.property⟩)
        (Prod.Lex.right _ ξ.property) e a).mpr
      simpa only [embedStage, hζξ] using ht
    · intro ht
      refine ⟨⟨ξ.val, ξ.property.trans_le (s.2.property.trans h)⟩, rfl, ?_⟩
      exact (ih (s.1, ⟨ξ.val, ξ.property.le.trans s.2.property⟩)
        (Prod.Lex.right _ ξ.property) e a).mp ht

theorem current_realize_of_previous {α κ : Ordinal.{u}} (h : α ≤ κ)
    (hα : Order.IsSuccLimit α)
    (he : letI := (@auxiliaryInterpretation κ (LStageZF κ)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF α)).IsElementary)
    (s : Stage α)
    (ih : ∀ t, Earlier t s → ∀ e a : ZFCarrier (LStageZF α),
      ZFSet.pair e.val a.val ∈ truth (LStageZF α) t ↔
        ZFSet.pair e.val a.val ∈ truth (LStageZF κ) (embedStage h t))
    {n : Nat} (φ : (language s.1 {ξ : Ordinal.{u} // ξ < s.2.val}).BoundedFormula Empty n)
    (xs : Fin n → ZFCarrier (LStageZF α)) :
    OneYTruth.realize (interpretation (LStageZF α) s) φ Empty.elim xs ↔
      OneYTruth.realize (interpretation (LStageZF κ) (embedStage h s)) φ Empty.elim
        (fun i => Auxiliary.inclusion (LStageZF_mono h) (xs i)) := by
  rw [← current_reduct_eq h hα s ih]
  have hp := Auxiliary.realize_restrict_reduct (@auxiliaryInterpretation κ (LStageZF κ))
    (LStageZF_mono h) he (traceBlock hα s.1) (traceIndex s) φ Empty.elim xs
  have hbig := auxiliaryReduct_interpretation (LStageZF κ) s.1 (s.2.property.trans h)
    (fun j => Auxiliary.inclusion (LStageZF_mono h) (traceBlock hα s.1 j)) (fun _ => rfl)
    (fun i => Auxiliary.inclusion (LStageZF_mono h) (traceIndex s i)) (fun _ => rfl)
  rw [hbig] at hp
  have hfree : (fun i : Empty => Auxiliary.inclusion (LStageZF_mono h)
      (Empty.elim i : ZFCarrier (LStageZF α))) = Empty.elim := by
    funext i
    nomatch i
  simpa only [hfree, embedStage] using hp

/-- The rebuilt small-domain tower agrees with the big-domain tower on every internal code. -/
theorem truth_trace {α κ : Ordinal.{u}} (h : α ≤ κ) (hα : Order.IsSuccLimit α)
    (he : letI := (@auxiliaryInterpretation κ (LStageZF κ)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF α)).IsElementary)
    (s : Stage α) : ∀ e a : ZFCarrier (LStageZF α),
      ZFSet.pair e.val a.val ∈ truth (LStageZF α) s ↔
        ZFSet.pair e.val a.val ∈ truth (LStageZF κ) (embedStage h s) := by
  induction s using (earlier_wellFounded α).induction with
  | h s ih =>
      intro e a
      rw [truth_eq_satisfactionSet, truth_eq_satisfactionSet]
      exact satisfactionSet_trace (LStageZF_mono h) (LStageZF_isTransitive α) ordinalIndexCode
        (interpretation (LStageZF κ) (embedStage h s)) (interpretation (LStageZF α) s)
        (fun _ φ xs => current_realize_of_previous h hα he s ih φ xs) e.val a.val a.property

theorem canonical_realize_trace {α κ : Ordinal.{u}} (h : α ≤ κ) (hα : Order.IsSuccLimit α)
    (he : letI := (@auxiliaryInterpretation κ (LStageZF κ)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF α)).IsElementary)
    (s : Stage α) {n : Nat}
    (φ : (language s.1 {ξ : Ordinal.{u} // ξ < s.2.val}).BoundedFormula Empty n)
    (xs : Fin n → ZFCarrier (LStageZF α)) :
    OneYTruth.realize (interpretation (LStageZF α) s) φ Empty.elim xs ↔
      OneYTruth.realize (interpretation (LStageZF κ) (embedStage h s)) φ Empty.elim
        (fun i => Auxiliary.inclusion (LStageZF_mono h) (xs i)) :=
  current_realize_of_previous h hα he s (fun t _ => truth_trace h hα he t) φ xs

/-- The whole restricted auxiliary predicate is the small domain's rebuilt uniform tower. -/
theorem canonical_auxiliary_restrict {α κ : Ordinal.{u}} (h : α ≤ κ)
    (hα : Order.IsSuccLimit α)
    (he : letI := (@auxiliaryInterpretation κ (LStageZF κ)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF α)).IsElementary) :
    Auxiliary.restrict (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF_mono h) =
      @auxiliaryInterpretation α (LStageZF α) := by
  change Auxiliary.Interpretation.mk _ _ = Auxiliary.Interpretation.mk _ _
  congr 1
  funext b ξ e a
  apply propext
  change ZFSet.pair (ZFSet.pair b.val ξ.val) (ZFSet.pair e.val a.val) ∈
    @uniformSet κ (LStageZF κ) ↔
    ZFSet.pair (ZFSet.pair b.val ξ.val) (ZFSet.pair e.val a.val) ∈
      @uniformSet α (LStageZF α)
  rw [mem_uniformSet_iff, mem_uniformSet_iff]
  constructor
  · rintro ⟨k, hb, ζ, hζ, ht⟩
    have hζα : ζ.val < α :=
      MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
        (by rw [← hζ]; exact ξ.property)
    exact ⟨k, hb, ⟨ζ.val, hζα⟩, hζ,
      (truth_trace h hα he (k, ⟨ζ.val, hζα.le⟩) e a).mpr ht⟩
  · rintro ⟨k, hb, ζ, hζ, ht⟩
    exact ⟨k, hb, ⟨ζ.val, ζ.property.trans_le h⟩, hζ,
      (truth_trace h hα he (k, ⟨ζ.val, ζ.property.le⟩) e a).mp ht⟩

theorem canonical_realize_trace_params {α κ : Ordinal.{u}} (h : α ≤ κ)
    (hα : Order.IsSuccLimit α)
    (he : letI := (@auxiliaryInterpretation κ (LStageZF κ)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation κ (LStageZF κ)) (LStageZF α)).IsElementary)
    (s : Stage α) {A : Type v} {n : Nat}
    (φ : (language s.1 {ξ : Ordinal.{u} // ξ < s.2.val}).BoundedFormula A n)
    (v : A → ZFCarrier (LStageZF α)) (xs : Fin n → ZFCarrier (LStageZF α)) :
    OneYTruth.realize (interpretation (LStageZF α) s) φ v xs ↔
      OneYTruth.realize (interpretation (LStageZF κ) (embedStage h s)) φ
        (fun i => Auxiliary.inclusion (LStageZF_mono h) (v i))
        (fun i => Auxiliary.inclusion (LStageZF_mono h) (xs i)) := by
  rw [← current_reduct_eq h hα s (fun t _ => truth_trace h hα he t)]
  have hp := Auxiliary.realize_restrict_reduct (@auxiliaryInterpretation κ (LStageZF κ))
    (LStageZF_mono h) he (traceBlock hα s.1) (traceIndex s) φ v xs
  have hbig := auxiliaryReduct_interpretation (LStageZF κ) s.1 (s.2.property.trans h)
    (fun j => Auxiliary.inclusion (LStageZF_mono h) (traceBlock hα s.1 j)) (fun _ => rfl)
    (fun i => Auxiliary.inclusion (LStageZF_mono h) (traceIndex s i)) (fun _ => rfl)
  rw [hbig] at hp
  exact hp

end OneYTruth.ExternalTower
