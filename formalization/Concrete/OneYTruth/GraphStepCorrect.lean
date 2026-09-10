import OneYTruth.GraphStepWitnesses

/-! Full exactness of one fixed formula for the actual graph-input truth step. -/

namespace OneYTruth.GraphStepMatrix

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open FormulaCode

universe u

noncomputable def inputParameters (κ : Ordinal.{u}) (U x q S : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (snoc (fixedParameters κ U) x) q) S

theorem appended_base (κ : Ordinal.{u}) (U x q S : LCarrier.{u}) (w : Tuple LCarrier.{u} 18) :
    BaseParameters κ U (Fin.append (inputParameters κ U x q S) w) := by
  have hp (i : Fin 13) : Fin.append (inputParameters κ U x q S) w (Fin.castAdd 21 i) =
      fixedParameters κ U i := by
    change Fin.append (inputParameters κ U x q S) w
      (Fin.castAdd 18 i.castSucc.castSucc.castSucc) = _
    rw [Fin.append_left]
    simp only [inputParameters,snoc_castSucc]
  exact ⟨hp 0,hp 1,hp 2,congrArg (fun x : LCarrier.{u} => x.val) (hp 3),
    congrArg (fun x : LCarrier.{u} => x.val) (hp 4),
    hp 5,hp 6,hp 7,hp 8,hp 9,hp 10,hp 11,hp 12⟩

theorem formula_correct (κ η : Ordinal.{u}) (hηκ : η ≤ κ) (k : Nat)
    (U x q S : LCarrier.{u}) (hx : x.val = ZFSet.pair (natCode k) η.toZFSet) :
    FOFormula.Satisfies lCarrierMem formula
      (snoc (snoc (snoc (fixedParameters κ U) x) q) S) ↔
      S.val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet q.val := by
  rw [satisfies_formula]
  constructor
  · rintro ⟨w,hw⟩
    exact checks_sound κ η hηκ k U _ (appended_base κ U x q S w) hx hw
  · intro hS
    let p := canonicalContext κ η k U q S
    let w : Tuple LCarrier.{u} 18 := fun i => p (Fin.natAdd 16 i)
    have hpref : (fun i : Fin 16 => p (Fin.castAdd 18 i)) = inputParameters κ U x q S := by
      funext i
      fin_cases i <;> first | exact Subtype.ext hx.symm | rfl
    have he : Fin.append (inputParameters κ U x q S) w = p := by
      rw [← hpref]
      exact Fin.append_castAdd_natAdd
    refine ⟨w, ?_⟩
    change Checks (Fin.append (inputParameters κ U x q S) w)
    rw [he]
    exact canonicalContext_checks κ η hηκ k U q S hS

end OneYTruth.GraphStepMatrix
