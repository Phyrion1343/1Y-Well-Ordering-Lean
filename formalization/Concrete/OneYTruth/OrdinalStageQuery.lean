import OneYTruth.OrdinalHistoryWitnessBound
import OneYTruth.FiniteWitnessReflection

/-! # A literal Sigma-one query for an ordinal L-stage

Four exposed coordinates are a, omega, zero, proposed U. Four existential
witnesses are the common Def certificate bound, the successor index set,
the actual history, and its field container. The remaining bounded Def
matrix is explicit and is to be instantiated with the real certificate.
-/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.Godel
open RootSemantics

universe u v

/-- Params omega, zero, certificate-bound; then predecessor U and output D. -/
def boundedDefStep (δ : Delta0Formula 5) : Delta0Formula 5 := δ.rename ![3,0,1,4,2]

theorem satisfies_boundedDefStep (δ : Delta0Formula 5) (omega zero W U D : ZFSet.{u}) :
    Satisfies ZFMem (boundedDefStep δ) (snoc (snoc ![omega,zero,W] U) D) ↔
      Satisfies ZFMem δ ![U,omega,zero,D,W] := by
  rw [boundedDefStep,satisfies_rename]
  have he : (fun i => snoc (snoc ![omega,zero,W] U) D (![3,0,1,4,2] i)) =
      ![U,omega,zero,D,W] := by funext i; fin_cases i <;> rfl
  rw [he]

def stageMatrix (δ : Delta0Formula 5) : Delta0Formula 8 :=
  .conj (successorAt 5 0) (.conj (entryAt 6 0 3)
    (historyAt (boundedDefStep δ) ![1,2,4] 5 6 7 2))

theorem satisfies_stageMatrix (δ : Delta0Formula 5) (a omega U W I g F : ZFSet.{u}) :
    Satisfies ZFMem (stageMatrix δ) ![a,omega,∅,U,W,I,g,F] ↔
      I = insert a a ∧ ZFSet.pair a U ∈ g ∧
        RawChecks (fun S D => Satisfies ZFMem δ ![S,omega,∅,D,W]) I g F := by
  simp only [stageMatrix,Satisfies,satisfies_successorAt,satisfies_entryAt]
  rw [satisfies_historyAt (boundedDefStep δ) ![1,2,4] 5 6 7 2 _ (by rfl)]
  have he : (fun i : Fin 3 => (![a,omega,∅,U,W,I,g,F] : Fin 8 → ZFSet.{u}) (![1,2,4] i)) =
      ![omega,∅,W] := by funext i; fin_cases i <;> rfl
  rw [he]
  simp only [satisfies_boundedDefStep]
  rfl

theorem stageMatrix_sound (δ : Delta0Formula 5) {V : ZFSet.{u}} (hV : V.IsTransitive)
    (a : Ordinal.{u}) {U W I g F : ZFSet.{u}} (hg : g ∈ V) (hW : W ∈ V)
    (hδ : ∀ S ∈ V, ∀ D ∈ V, ∀ B ∈ V,
      Satisfies ZFMem δ ![S,Ordinal.omega0.toZFSet,∅,D,B] → D = DefZF S)
    (h : Satisfies ZFMem (stageMatrix δ)
      ![a.toZFSet,Ordinal.omega0.toZFSet,∅,U,W,I,g,F]) : U = LStageZF a := by
  obtain ⟨hI,hentry,hchecks⟩ := (satisfies_stageMatrix δ _ _ _ _ _ _ _).mp h
  have hI' : I = (Order.succ a).toZFSet :=
    hI.trans ((ordinalToZFSet_successor_predecessor_iff a a.toZFSet).mpr rfl).symm
  rw [hI'] at hchecks
  exact top_eq_of_internal hV hg (fun S hS D hD => hδ S hS D hD W hW) hchecks.toChecks hentry

def stageQuery (K : Nat) (J : Type v) (δ : Delta0Formula 5) :=
  existsSuffix 4 (ofConstructibleDeltaZero K J (stageMatrix δ))

theorem stageQuery_isSigmaOne (K : Nat) (J : Type v) (δ : Delta0Formula 5) :
    IsSigmaOne (stageQuery K J δ) :=
  existsSuffix_isSigmaOne _ (.deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _))

theorem stageQuery_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (δ : Delta0Formula 5) (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (a : Ordinal.{u}) (p : Fin 4 → ZFCarrier V)
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅)
    (hδ : ∀ S ∈ V, ∀ D ∈ V, ∀ B ∈ V,
      Satisfies ZFMem δ ![S,Ordinal.omega0.toZFSet,∅,D,B] → D = DefZF S)
    (h : realize N (stageQuery K J δ) Empty.elim p) : (p 3).val = LStageZF a := by
  obtain ⟨w,hw⟩ := (realize_existsSuffix (m := 4) N (ofConstructibleDeltaZero K J (stageMatrix δ)) p).mp h
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem] at hw
  have he : val (Fin.append p w) =
      ![a.toZFSet,Ordinal.omega0.toZFSet,∅,(p 3).val,(w 0).val,(w 1).val,(w 2).val,(w 3).val] := by
    funext i
    fin_cases i <;> first | exact ha | exact hOmega | exact hZero | rfl
  rw [he] at hw
  exact stageMatrix_sound δ hV a (w 2).property (w 0).property hδ hw

theorem stageQuery_complete {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (δ : Delta0Formula 5) (hβ : Adequate β)
    (N : Interpretation K J (ZFCarrier (LStageZF β))) (hmem : N.mem = zfCarrierMem (LStageZF β))
    (a : Ordinal.{u}) (haβ : a < β) (p : Fin 4 → ZFCarrier (LStageZF β))
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (hU : (p 3).val = LStageZF a)
    (hmono : ∀ S D B C : ZFSet.{u}, B ⊆ C →
      Satisfies ZFMem δ ![S,Ordinal.omega0.toZFSet,∅,D,B] →
      Satisfies ZFMem δ ![S,Ordinal.omega0.toZFSet,∅,D,C])
    (hlocal : ∀ i < a, ∃ B ∈ LStageZF β,
      Satisfies ZFMem δ ![LStageZF i,Ordinal.omega0.toZFSet,∅,LStageZF (Order.succ i),B]) :
    realize N (stageQuery K J δ) Empty.elim p := by
  obtain ⟨W,hW,hWδ⟩ := exists_uniform_Def_bound δ hβ haβ hmono hlocal
  let g := canonicalBareHistory a
  let F := pairField g
  let I := (Order.succ a).toZFSet
  let w : Fin 4 → ZFCarrier (LStageZF β) :=
    ![⟨W,hW⟩,⟨I,ordinal_toZFSet_mem_LStageZF_of_lt (hβ.2.1.succ_lt haβ)⟩,
      ⟨g,canonical_mem_of_adequate hβ haβ⟩,⟨F,history_field_mem_of_limit hβ.2.1 haβ⟩]
  apply (realize_existsSuffix (m := 4) N (ofConstructibleDeltaZero K J (stageMatrix δ)) p).mpr
  refine ⟨w,?_⟩
  rw [realize_ofConstructibleDeltaZero_absolute (LStageZF_isTransitive β) N hmem]
  have he : val (Fin.append p w) =
      ![a.toZFSet,Ordinal.omega0.toZFSet,∅,LStageZF a,W,I,g,F] := by
    funext i
    fin_cases i <;> first | exact ha | exact hOmega | exact hZero | exact hU | rfl
  rw [he,satisfies_stageMatrix]
  exact ⟨(ordinalToZFSet_successor_predecessor_iff a a.toZFSet).mpr rfl,
    canonicalBareHistory_top_mem a, canonical_rawChecks a (canonical_stage_mem_field a)
      (fun i hi => hWδ i (Order.succ_le_iff.mp hi))⟩

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.stageQuery_isSigmaOne
#print axioms OneYTruth.OrdinalStageHistory.stageQuery_sound
#print axioms OneYTruth.OrdinalStageHistory.stageQuery_complete

