import OneYTruth.TarskiCertificate
import OneYTruth.ExternalTower

/-!
# Uniqueness of a mixed tower satisfying its local recursion certificates

This closes the mathematical uniqueness argument for the entire bounded
external tower. It is still an external certificate on a set-sized family,
not a claimed internal Sigma-one definition or constructible-level theorem.
-/

namespace OneYTruth.ExternalTower

open Constructible FormulaCode

universe u

/-- Every stage is a Tarski set for the structure defined by earlier stages. -/
def IsTowerFamily {κ : Ordinal.{u}} (U : ZFSet.{u}) (T : Stage κ → ZFSet.{u}) : Prop :=
  ∀ s, IsTarskiSet ordinalIndexCode
    (stageInterpretation U s (fun t _ => T t)) (T s)

theorem truth_isTowerFamily {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    IsTowerFamily U (@truth κ U) := by
  intro s
  change IsTarskiSet ordinalIndexCode (interpretation U s) (truth U s)
  rw [truth_eq_satisfactionSet]
  exact satisfactionSet_isTarskiSet ordinalIndexCode_injective _

/-- Local certificates determine all stages, using the already proved stage order. -/
theorem IsTowerFamily.eq_truth {κ : Ordinal.{u}} {U : ZFSet.{u}}
    {T : Stage κ → ZFSet.{u}} (h : IsTowerFamily U T) : T = truth U := by
  funext s
  induction s using (earlier_wellFounded κ).induction with
  | h s ih =>
    have hprev : (fun t (_ : Earlier t s) => T t) =
        (fun t (_ : Earlier t s) => truth U t) := by
      funext t ht
      exact ih t ht
    calc
      T s = satisfactionSet ordinalIndexCode
          (stageInterpretation U s (fun t _ => T t)) :=
        (h s).eq_satisfactionSet ordinalIndexCode_injective
      _ = satisfactionSet ordinalIndexCode (interpretation U s) := by
        rw [hprev]
        rfl
      _ = truth U s := (truth_eq_satisfactionSet U s).symm

/-- The actual tower, rather than an assumed field, witnesses existence. -/
theorem existsUnique_towerFamily {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    ∃! T : Stage κ → ZFSet.{u}, IsTowerFamily U T :=
  ⟨truth U, truth_isTowerFamily U, fun _ h => h.eq_truth⟩

end OneYTruth.ExternalTower
