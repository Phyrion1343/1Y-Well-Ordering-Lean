import OneYTruth.OrdinalHistoryRecovery

/-! # Collection produces one common bound for all Def steps of an L-history

The local input is an actual native bounded Def certificate. Pointwise
internal witness existence and monotonicity in its last bound coordinate
are enough; no externally chosen witness family is assumed internal.
-/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.Godel
open RootSemantics InternalClosure

universe u

/-- Layout omega, zero, index-source, history, field, index, witness-bound.
Bounded locals are next-index, predecessor-stage, next-stage. -/
def localBoundFormula (δ : Delta0Formula 5) : Delta0Formula 7 :=
  .boundedAll 2 (.imp (successorAt 7 5)
    (.boundedAll 4 (.boundedAll 4
      (.imp (.conj (entryAt 3 5 8) (entryAt 3 7 9))
        (δ.rename ![8,0,1,9,6])))))

theorem satisfies_localBoundFormula (δ : Delta0Formula 5)
    (omega zero I g F i B : ZFSet.{u}) :
    Satisfies ZFMem (localBoundFormula δ) ![omega,zero,I,g,F,i,B] ↔
      ∀ j ∈ I, j = insert i i → ∀ U ∈ F, ∀ D ∈ F,
        ZFSet.pair i U ∈ g → ZFSet.pair j D ∈ g →
          Satisfies ZFMem δ ![U,omega,zero,D,B] := by
  have hmatrix (j U D : ZFSet.{u}) :
      (fun k => snoc (snoc (snoc ![omega,zero,I,g,F,i,B] j) U) D (![8,0,1,9,6] k)) =
        ![U,omega,zero,D,B] := by
    funext k
    fin_cases k <;> rfl
  simp only [localBoundFormula, satisfies_boundedAll, satisfies_imp, satisfies_successorAt,
    Satisfies, satisfies_entryAt, satisfies_rename, hmatrix]
  constructor
  · intro h j hj hs U hU D hD he hf
    exact h j hj hs U hU D hD ⟨he,hf⟩
  · intro h j hj hs U hU D hD ⟨he,hf⟩
    exact h j hj hs U hU D hD he hf

theorem exists_uniform_Def_bound (δ : Delta0Formula 5) {a β : Ordinal.{u}}
    (hβ : Adequate β) (ha : a < β)
    (hmono : ∀ U D B C : ZFSet.{u}, B ⊆ C →
      Satisfies ZFMem δ ![U,Ordinal.omega0.toZFSet,∅,D,B] →
      Satisfies ZFMem δ ![U,Ordinal.omega0.toZFSet,∅,D,C])
    (hlocal : ∀ i < a, ∃ B ∈ LStageZF β,
      Satisfies ZFMem δ ![LStageZF i,Ordinal.omega0.toZFSet,∅,LStageZF (Order.succ i),B]) :
    ∃ W ∈ LStageZF β, ∀ i < a,
      Satisfies ZFMem δ ![LStageZF i,Ordinal.omega0.toZFSet,∅,LStageZF (Order.succ i),W] := by
  let V := LStageZF β
  let N := ExternalTower.interpretation (κ := β) V (0, ⟨0, zero_le⟩)
  have hV : V.IsTransitive := LStageZF_isTransitive β
  have hCol : HasCollection N := (hβ.2.2 0 0 zero_le).2
  let I := (Order.succ a).toZFSet
  let g := canonicalBareHistory a
  let F := pairField g
  have hI : I ∈ V := ordinal_toZFSet_mem_LStageZF_of_lt (hβ.2.1.succ_lt ha)
  have hg : g ∈ V := canonical_mem_of_adequate hβ ha
  have hF : F ∈ V := history_field_mem_of_limit hβ.2.1 ha
  have hOmega : Ordinal.omega0.toZFSet ∈ V := ordinal_toZFSet_mem_LStageZF_of_lt hβ.1
  have hzero : (∅ : ZFSet.{u}) ∈ V := empty_mem_LStageZF_of_isSuccLimit hβ.2.1
  let params : Fin 5 → ZFCarrier V := ![⟨Ordinal.omega0.toZFSet,hOmega⟩,⟨∅,hzero⟩,
    ⟨I,hI⟩,⟨g,hg⟩,⟨F,hF⟩]
  let source : ZFCarrier V := ⟨a.toZFSet,ordinal_toZFSet_mem_LStageZF_of_lt ha⟩
  let φ := ofConstructibleDeltaZero 0 {ξ : Ordinal.{u} // ξ < 0} (localBoundFormula δ)
  have hsem (x B : ZFCarrier V) :
      realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) B) ↔
        ∀ j ∈ I, j = insert x.val x.val → ∀ U ∈ F, ∀ D ∈ F,
          ZFSet.pair x.val U ∈ g → ZFSet.pair j D ∈ g →
            Satisfies ZFMem δ ![U,Ordinal.omega0.toZFSet,∅,D,B.val] := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N rfl]
    have he : val (Fin.snoc (Fin.snoc params x) B) =
        ![Ordinal.omega0.toZFSet,∅,I,g,F,x.val,B.val] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact satisfies_localBoundFormula δ _ _ _ _ _ _ _
  have hpoint (x : ZFCarrier V) (hx : x.val ∈ source.val) :
      ∃ B : ZFCarrier V, realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) B) := by
    obtain ⟨i, hia, hi⟩ := Ordinal.mem_toZFSet_iff.mp hx
    obtain ⟨B,hBV,hBδ⟩ := hlocal i hia
    refine ⟨⟨B,hBV⟩,(hsem x ⟨B,hBV⟩).mpr ?_⟩
    intro j hj hs U _ D _ hU hD
    have hU' : U = LStageZF i := by
      obtain ⟨k, _, hk, hUk⟩ := pair_mem_canonicalBareHistory_iff.mp hU
      exact hUk.trans (congrArg LStageZF (Ordinal.toZFSet_injective (hk.symm.trans hi.symm)))
    have hjEq : j = (Order.succ i).toZFSet := by
      rw [hs, ← hi]
      exact ((ordinalToZFSet_successor_predecessor_iff i i.toZFSet).mpr rfl).symm
    have hD' : D = LStageZF (Order.succ i) := by
      obtain ⟨k, _, hk, hDk⟩ := pair_mem_canonicalBareHistory_iff.mp hD
      exact hDk.trans (congrArg LStageZF (Ordinal.toZFSet_injective (hk.symm.trans hjEq)))
    simpa only [hU',hD'] using hBδ
  obtain ⟨C,hC⟩ := hCol 5 φ params source hpoint
  let W := ZFSet.sUnion C.val
  have hW : W ∈ V := sUnion_mem_LStageZF_of_isSuccLimit hβ.2.1 C.property
  refine ⟨W,hW,?_⟩
  intro i hia
  let x : ZFCarrier V := ⟨i.toZFSet,ordinal_toZFSet_mem_LStageZF_of_lt (hia.trans ha)⟩
  obtain ⟨B,hBC,hB⟩ := hC x (Ordinal.toZFSet_mem_toZFSet_iff.mpr hia)
  have hstep := (hsem x B).mp hB (Order.succ i).toZFSet
    (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr (Order.succ_le_iff.mpr hia)))
    ((ordinalToZFSet_successor_predecessor_iff i i.toZFSet).mpr rfl)
    (LStageZF i) (canonical_stage_mem_field a i hia.le)
    (LStageZF (Order.succ i)) (canonical_stage_mem_field a _ (Order.succ_le_iff.mpr hia))
    (pair_mem_canonicalBareHistory_iff.mpr ⟨i,hia.le,rfl,rfl⟩)
    (pair_mem_canonicalBareHistory_iff.mpr ⟨Order.succ i,Order.succ_le_iff.mpr hia,rfl,rfl⟩)
  exact hmono _ _ B.val W (fun z hz => ZFSet.mem_sUnion.mpr ⟨B.val,hBC,hz⟩) hstep

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.exists_uniform_Def_bound
