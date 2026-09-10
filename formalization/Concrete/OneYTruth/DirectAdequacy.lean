import OneYTruth.BoundedOrdinal

/-!
# A complete bounded adequacy check on the actual canonical parameters

Even the ordinal and limit requirements are checked by literal bounded
formulas. Canonicality and internal existence of the supplied domain and
bundle are still separate obligations, not hypotheses silently discharged.
-/

namespace OneYTruth.DirectAdequacy

open Constructible Constructible.Delta0Formula FirstOrder FirstOrder.Language
open RootSemantics ExternalTower SchemaBundle BoundedOrdinal

universe u v

/-- Omega, ordinal code, domain, actual schema bundle, its field bound. -/
def formula : Delta0Formula 5 :=
  .conj (Delta0Formula.rename ![0, 1] aboveOmegaLimitFormula)
    (Delta0Formula.rename ![2, 3, 4] SchemaBundle.formula)

noncomputable def parameters (a : Ordinal.{u}) : Fin 5 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, a.toZFSet, LStageZF a,
    @bundle a (LStageZF a), @fieldBound a (LStageZF a)]

theorem satisfies_formula (a : Ordinal.{u}) :
    Satisfies ZFMem formula (parameters a) ↔ Adequate a := by
  have hfirst : (fun i : Fin 2 => parameters a (![0, 1] i)) =
      ![Ordinal.omega0.toZFSet, a.toZFSet] := by
    funext i
    fin_cases i <;> rfl
  have hsecond : (fun i : Fin 3 => parameters a (![2, 3, 4] i)) =
      ![LStageZF a, @bundle a (LStageZF a), @fieldBound a (LStageZF a)] := by
    funext i
    fin_cases i <;> rfl
  simp only [formula, Satisfies, Delta0Formula.satisfies_rename]
  rw [hfirst, hsecond, satisfies_aboveOmegaLimitFormula]
  constructor
  · rintro ⟨⟨hω, hlim⟩, h⟩
    haveI : Nonempty (ZFCarrier (LStageZF a)) :=
      ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit hlim⟩⟩
    have hs := (satisfies_canonical_bundle_iff (LStageZF a)).mp h
    exact ⟨hω, hlim, fun k η hηa => hs (k, ⟨η, hηa⟩)⟩
  · intro h
    haveI : Nonempty (ZFCarrier (LStageZF a)) :=
      ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit h.2.1⟩⟩
    exact ⟨⟨h.1, h.2.1⟩, (satisfies_canonical_bundle_iff (LStageZF a)).mpr
      (fun s => h.2.2 s.1 s.2.val s.2.property)⟩

def mixedFormula (K : Nat) (J : Type v) := ofConstructibleDeltaZero K J formula

theorem mixedFormula_isDeltaZero (K : Nat) (J : Type v) : IsDeltaZero (mixedFormula K J) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_iff_adequate (a : Ordinal.{u})
    {W : ZFSet.{u}} {K : Nat} {J : Type v} (hW : W.IsTransitive)
    (N : Interpretation K J (ZFCarrier W)) (hmem : N.mem = zfCarrierMem W)
    (p : Fin 5 → ZFCarrier W) (hp : ∀ i, (p i).val = parameters a i) :
    realize N (mixedFormula K J) Empty.elim p ↔ Adequate a := by
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute hW N hmem]
  have he : Delta0Formula.val p = parameters a := funext hp
  rw [he]
  exact satisfies_formula a

end OneYTruth.DirectAdequacy

#print axioms OneYTruth.DirectAdequacy.mixedFormula_isDeltaZero
#print axioms OneYTruth.DirectAdequacy.realize_iff_adequate
