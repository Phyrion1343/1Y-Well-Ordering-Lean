import OneYTruth.CanonicalEvaluationHistory

/-!
# The complete set of finite evaluation approximations is internal

The uniform two-existential history formula is constructed explicitly.
Collection and Separation then supply its actual Replacement instance,
which collects the whole natural-number family. No family-membership or
recursion-existence field is assumed.
-/

namespace OneYTruth.BoundedEvaluation

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF InternalClosure

universe u v

noncomputable def queryParameters (D : Diagram.{u}) (n S : ZFSet.{u}) : Tuple ZFSet.{u} 10 :=
  ![D.nodes, D.atoms, D.trueAtoms, D.implications, D.quantified, D.children,
    Ordinal.omega0.toZFSet, ∅, n, S]

def historyQueryMatrix : Delta0Formula 12 :=
  .conj (Delta0Formula.rename ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11] historyFormula)
    (pairMemAt 10 8 9)

theorem satisfies_historyQueryMatrix (D : Diagram.{u}) (n S H B : ZFSet.{u}) :
    Satisfies ZFMem historyQueryMatrix
      (Constructible.snoc (Constructible.snoc (queryParameters D n S) H) B) ↔
      IsHistory D H B ∧ ZFSet.pair n S ∈ H := by
  change (Satisfies ZFMem
      (Delta0Formula.rename ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11] historyFormula) _ ∧
    Satisfies ZFMem (pairMemAt 10 8 9) _) ↔ _
  rw [satisfies_rename, satisfies_pairMemAt]
  have heq : (fun i => Constructible.snoc (Constructible.snoc (queryParameters D n S) H) B
      (![0, 1, 2, 3, 4, 5, 6, 7, 10, 11] i)) = historyParameters D H B := by
    funext i
    fin_cases i <;> rfl
  rw [heq, satisfies_historyFormula]
  rfl

def historyQuery (k : Nat) (I : Type v) : (language k I).BoundedFormula Empty 10 :=
  (ofConstructibleDeltaZero k I historyQueryMatrix).ex.ex

theorem historyQuery_isSigmaOne (k : Nat) (I : Type v) :
    IsSigmaOne (historyQuery k I) :=
  .ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero k I historyQueryMatrix)))

theorem realize_historyQuery {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (D : Diagram.{u}) (n S : ZFSet.{u})
    (p : Fin 10 → ZFCarrier V) (hp : ∀ i, (p i).val = queryParameters D n S i) :
    OneYTruth.realize N (historyQuery k I) Empty.elim p ↔
      ∃ H B : ZFCarrier V, IsHistory D H.val B.val ∧ ZFSet.pair n S ∈ H.val := by
  have hc (H B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero k I historyQueryMatrix) Empty.elim
        (Fin.snoc (Fin.snoc p H) B) ↔ IsHistory D H.val B.val ∧ ZFSet.pair n S ∈ H.val := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    have heq : Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc p H) B) =
        Constructible.snoc (Constructible.snoc (queryParameters D n S) H.val) B.val := by
      rw [constructible_snoc_eq, constructible_snoc_eq]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Constructible.Delta0Formula.val, Fin.snoc_last]
      · refine Fin.lastCases ?_ (fun l => ?_) j
        · simp only [Constructible.Delta0Formula.val, Fin.snoc_last, Fin.snoc_castSucc]
        · simpa only [Constructible.Delta0Formula.val, Fin.snoc_castSucc] using hp l
    rw [heq]
    exact satisfies_historyQueryMatrix D n S H.val B.val
  letI := N.structure
  change (ofConstructibleDeltaZero k I historyQueryMatrix).ex.ex.Realize Empty.elim p ↔ _
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro H
  rw [BoundedFormula.realize_ex]
  exact exists_congr (hc H)

theorem range_natCode_eq_omega :
    ZFSet.range (natCode : Nat → ZFSet.{u}) = Ordinal.omega0.toZFSet := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_range, mem_omega_iff_exists_natCode]
  simp only [eq_comm]

noncomputable def evaluationFamily (D : Diagram.{u}) : ZFSet.{u} := ZFSet.range (iterate D)

theorem evaluationFamily_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hOmega : Ordinal.omega0.toZFSet ∈ V)
    (D : Diagram.{u}) (hD : ∀ i, parameters D ∅ i ∈ V) : evaluationFamily D ∈ V := by
  have hempty : (∅ : ZFSet.{u}) ∈ V := hD 0
  have hNat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩) hOmega
  have hstep := hSep 7 (mixedStepFormula k I)
  have hIter (n : Nat) := iterate_mem hV N hmem hstep hempty D hD n
  have hH (n : Nat) := finiteHistory_mem hV N hmem hstep hpair hUnion hempty hNat D hD n
  have hB (n : Nat) := historyContainer_mem hV N hmem hstep hpair hUnion hempty hNat D hD n
  let params : Fin 8 → ZFCarrier V :=
    ![⟨D.nodes, hD 1⟩, ⟨D.atoms, hD 2⟩, ⟨D.trueAtoms, hD 3⟩,
      ⟨D.implications, hD 4⟩, ⟨D.quantified, hD 5⟩, ⟨D.children, hD 6⟩,
      ⟨Ordinal.omega0.toZFSet, hOmega⟩, ⟨∅, hempty⟩]
  have hsource : ZFSet.range (natCode : Nat → ZFSet.{u}) ∈ V := by
    rw [range_natCode_eq_omega]
    exact hOmega
  apply image_range_mem hV N (historyQuery k I)
    (hasReplacement_of_collection_separation N hmem hCol hSep 8 (historyQuery k I))
    params natCode (iterate D) natCode_injective hsource hIter
  intro x y hx
  have hp : ∀ i, ((Fin.snoc (Fin.snoc params x) y : Fin 10 → ZFCarrier V) i).val =
      queryParameters D x.val y.val i := by
    intro i
    fin_cases i <;> rfl
  rw [realize_historyQuery hV N hmem D x.val y.val _ hp]
  constructor
  · rintro ⟨H, B, hh, hxy⟩
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp hx
    have hny : ZFSet.pair (natCode n) y.val ∈ H.val := hn.symm ▸ hxy
    exact ⟨n, hn, (hh.value_eq_iterate n hny).symm⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨⟨finiteHistory D n, hH n⟩, ⟨historyContainer D n, hB n⟩,
      finiteHistory_isHistory D n, ?_⟩
    rw [← hn, ← hny]
    exact last_mem_finiteHistory D n

end OneYTruth.BoundedEvaluation
