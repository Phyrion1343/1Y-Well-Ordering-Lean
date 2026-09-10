import OneYTruth.SatisfactionSet
import Mathlib.Order.RelClasses

/-!
# A bounded external mixed truth tower

For a fixed set domain `U` and a fixed ordinal bound `κ`, every block and
stage is defined by one well-founded recursion on `Nat × (κ + 1)`. Every
value is an actual `ZFSet`, obtained from `satisfactionSet`. The graph of
the whole family is also a `ZFSet`, by proved smallness of the index type.

This is not an assertion that the truth sets or their graph belong to a
specified constructible level. No admissibility, reflection, or elementary
submodel existence is assumed here.
-/

namespace OneYTruth.ExternalTower

open FirstOrder FirstOrder.Language Constructible FormulaCode

universe u

/-- All finite blocks and stages at most a fixed ordinal bound. -/
abbrev Stage (κ : Ordinal.{u}) := Nat × {η : Ordinal.{u} // η ≤ κ}

/-- A lower block may use any stage; within one block the stage decreases. -/
def Earlier {κ : Ordinal.{u}} : Stage κ → Stage κ → Prop :=
  Prod.Lex (· < ·) (fun η ξ => η.val < ξ.val)

theorem earlier_wellFounded (κ : Ordinal.{u}) : WellFounded (@Earlier κ) :=
  Nat.lt_wfRel.wf.prod_lex (InvImage.wf Subtype.val Ordinal.lt_wf)

noncomputable instance stageSmall (κ : Ordinal.{u}) : Small.{u} (Stage κ) :=
  inferInstanceAs (Small.{u} (Nat × {η : Ordinal.{u} // η ≤ κ}))

/-- Build the interpretation at a stage from the genuinely earlier truth sets. -/
def stageInterpretation {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ)
    (previous : ∀ t, Earlier t s → ZFSet.{u}) :
    Interpretation s.1 {ξ : Ordinal.{u} // ξ < s.2.val} (ZFCarrier U) where
  mem a b := a.val ∈ b.val
  named ξ e a := ZFSet.pair e.val a.val ∈
    previous (s.1, ⟨ξ.val, le_trans ξ.property.le s.2.property⟩)
      (Prod.Lex.right _ ξ.property)
  diagonal j ξCode e a := ∃ ξ : {ξ : Ordinal.{u} // ξ < κ},
    ξCode.val = ξ.val.toZFSet ∧ ZFSet.pair e.val a.val ∈
      previous (j.val, ⟨ξ.val, ξ.property.le⟩) (Prod.Lex.left _ _ j.isLt)

/-- One recursive step constructs full satisfaction rather than postulating it. -/
noncomputable def step {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ)
    (previous : ∀ t, Earlier t s → ZFSet.{u}) : ZFSet.{u} :=
  satisfactionSet ordinalIndexCode (stageInterpretation U s previous)

/-- The actual truth set at every bounded stage and finite block. -/
noncomputable def truth {κ : Ordinal.{u}} (U : ZFSet.{u}) : Stage κ → ZFSet.{u} :=
  (earlier_wellFounded κ).fix (step U)

/-- The canonical structure resulting from this external recursion. -/
noncomputable def interpretation {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :=
  stageInterpretation U s (fun t _ => truth U t)

theorem truth_eq_satisfactionSet {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :
    truth U s = satisfactionSet ordinalIndexCode (interpretation U s) :=
  WellFounded.fix_eq (earlier_wellFounded κ) (step U) s

/-- Full formula truth at a canonical stage agrees with membership in its truth set. -/
theorem mem_truth_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) {n : Nat}
    (φ : (language s.1 {ξ : Ordinal.{u} // ξ < s.2.val}).BoundedFormula Empty n)
    (v : Fin n → ZFCarrier U) :
    ZFSet.pair (packedCode ordinalIndexCode ⟨n, φ⟩) (assignmentCode v) ∈ truth U s ↔
      OneYTruth.realize (interpretation U s) φ Empty.elim v := by
  rw [truth_eq_satisfactionSet]
  exact mem_satisfactionSet_iff ordinalIndexCode_injective _ _ _

/-- A literal set code for a stage index. -/
noncomputable def stageCode {κ : Ordinal.{u}} (s : Stage κ) : ZFSet.{u} :=
  ZFSet.pair (Constructible.FiniteSequenceZF.natCode s.1) s.2.val.toZFSet

theorem stageCode_injective {κ : Ordinal.{u}} :
    Function.Injective (@stageCode κ) := by
  intro s t h
  obtain ⟨hk, hη⟩ := ZFSet.pair_inj.mp h
  apply Prod.ext
  · exact Constructible.FiniteSequenceZF.natCode_injective hk
  · exact Subtype.ext (Ordinal.toZFSet_injective hη)

/-- The whole bounded tower is a set of stage/truth-set pairs. -/
noncomputable def graph {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun s : Stage κ => ZFSet.pair (stageCode s) (truth U s))

theorem mem_graph_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) (T : ZFSet.{u}) :
    ZFSet.pair (stageCode s) T ∈ @graph κ U ↔ T = truth U s := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := ZFSet.mem_range.mp h
    obtain ⟨hst, hT⟩ := ZFSet.pair_inj.mp ht
    have hts : t = s := stageCode_injective hst
    subst t
    exact hT.symm
  · intro h
    subst T
    exact ZFSet.mem_range_self (f := fun t : Stage κ =>
      ZFSet.pair (stageCode t) (truth U t)) s

end OneYTruth.ExternalTower
