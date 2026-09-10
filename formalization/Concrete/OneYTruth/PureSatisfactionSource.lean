import OneYTruth.PureSatisfactionMatrix
import OneYTruth.SyntaxSourceCertificate
import OneYTruth.AssignmentSourceCertificate
import OneYTruth.LookupSourceCertificate
import OneYTruth.FiniteWitnessReflection

/-! Pure satisfaction from four primitive parameters. Complete syntax,
assignments, lookup, and all diagram sources are existentially checked. -/

namespace OneYTruth.PureSatisfactionSource

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open PureSatisfactionMatrix FormulaCode InternalNodes AssignmentLookup

universe u v

noncomputable def syntaxAt (K : Nat) (J : Type v) :=
  renameScope ![2,1,2,2,(10 : Fin 22)] (SyntaxSourceCertificate.query.{u,v} .full K J)
noncomputable def assignmentAt (K : Nat) (J : Type v) :=
  renameScope ![0,1,2,(11 : Fin 22)] (AssignmentSourceCertificate.query.{u,v} K J)
noncomputable def lookupAt (K : Nat) (J : Type v) :=
  renameScope ![0,1,2,(12 : Fin 22)] (LookupSourceCertificate.query.{u,v} K J)
def matrixAt (K : Nat) (J : Type v) := ofConstructibleDeltaZero K J matrix

theorem syntaxAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (syntaxAt.{u,v} K J) :=
  (SyntaxSourceCertificate.query_isSigmaOne .full K J).renameScope _
theorem assignmentAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (assignmentAt.{u,v} K J) :=
  (AssignmentSourceCertificate.query_isSigmaOne K J).renameScope _
theorem lookupAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (lookupAt.{u,v} K J) :=
  (LookupSourceCertificate.query_isSigmaOne K J).renameScope _
theorem matrixAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (matrixAt K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

noncomputable def leftBody (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (syntaxAt.{u,v} K J) (assignmentAt.{u,v} K J)
    (syntaxAt_isSigmaOne K J) (assignmentAt_isSigmaOne K J)
noncomputable def rightBody (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (lookupAt.{u,v} K J) (matrixAt K J)
    (lookupAt_isSigmaOne K J) (matrixAt_isSigmaOne K J)
noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (leftBody.{u,v} K J) (rightBody.{u,v} K J)
    (sigmaConjFormula_isSigmaOne _ _ _ _) (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_body {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 22 → A) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      realize N (SyntaxSourceCertificate.query.{u,v} .full K J) Empty.elim
        ![p 2,p 1,p 2,p 2,p 10] ∧
      realize N (AssignmentSourceCertificate.query.{u,v} K J) Empty.elim
        ![p 0,p 1,p 2,p 11] ∧
      realize N (LookupSourceCertificate.query.{u,v} K J) Empty.elim
        ![p 0,p 1,p 2,p 12] ∧
      realize N (matrixAt K J) Empty.elim p := by
  unfold body leftBody rightBody
  rw [realize_sigmaConjFormula,realize_sigmaConjFormula,realize_sigmaConjFormula]
  simp only [syntaxAt,assignmentAt,lookupAt,realize_renameScope]
  have hs : p ∘ ![2,1,2,2,(10 : Fin 22)] = ![p 2,p 1,p 2,p 2,p 10] := by
    funext i; fin_cases i <;> rfl
  have ha : p ∘ ![0,1,2,(11 : Fin 22)] = ![p 0,p 1,p 2,p 11] := by
    funext i; fin_cases i <;> rfl
  have hl : p ∘ ![0,1,2,(12 : Fin 22)] = ![p 0,p 1,p 2,p 12] := by
    funext i; fin_cases i <;> rfl
  rw [hs,ha,hl,and_assoc]

theorem body_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (U : LCarrier.{u}) (p : Fin 22 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (h : realize N (body.{u+1,v} K J) Empty.elim p) :
    (p 10).val = syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}) ∧
      (p 11).val = assignmentCodes (p 0).val ∧
      (p 14).val = scopedPairs (k := 0) (p 0).val (Empty.elim : Empty → ZFSet.{u}) ∧
      (p 3).val = satisfactionSet Empty.elim (interpretation (p 0).val) := by
  obtain ⟨hs,ha,hl,hm⟩ := (realize_body N p).mp h
  have hz : (p 2).val = Constructible.FiniteSequenceZF.natCode 0 := by
    simpa [Constructible.FiniteSequenceZF.natCode] using hZero
  have hF := SyntaxSourceCertificate.query_sound .full hV N hmem
    emptyLCarrier empty_range.symm ![p 2,p 1,p 2,p 2,p 10] hZero hOmega hZero hz hs
  have hA := AssignmentSourceCertificate.query_sound hV N hmem
    U ![p 0,p 1,p 2,p 11] hU hOmega hZero ha
  have hL := LookupSourceCertificate.query_sound hV N hmem
    U ![p 0,p 1,p 2,p 12] hU hOmega hZero hl
  change (p 10).val = syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}) at hF
  rw [← hU] at hA hL
  rw [matrixAt,realize_ofConstructibleDeltaZero_absolute hV N hmem,satisfies_matrix] at hm
  exact ⟨hF,hA,checks_sound (fun i => (p i).val) hOmega hZero hF hA hL hm⟩

/-- U, omega, zero, proposed Sat. -/
noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 4 :=
  existsSuffix 18 (body.{u,v} K J)

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  existsSuffix_isSigmaOne _ (body_isSigmaOne K J)

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (h : realize N (query.{u+1,v} K J) Empty.elim p) :
    (p 3).val = satisfactionSet Empty.elim (interpretation (p 0).val) := by
  obtain ⟨w,hw⟩ := (realize_existsSuffix (m := 18) N (body.{u+1,v} K J) p).mp h
  exact (body_sound hV N hmem U (Fin.append p w) hU hOmega hZero hw).2.2.2

end OneYTruth.PureSatisfactionSource
