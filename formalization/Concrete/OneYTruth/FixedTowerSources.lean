import OneYTruth.InternalActualStep
import OneYTruth.CodeUniverseCertificate
import OneYTruth.AssignmentSourceCertificate
import OneYTruth.LookupSourceCertificate
import OneYTruth.NaturalTagCertificate

/-! Normative checks of all thirteen shared tower sources. Only the original
domain, ordinal bound, omega, and zero are primitive inputs. -/

namespace OneYTruth.FixedTowerSources

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language InternalClosure UniformSyntaxSource GraphStepMatrix

universe u v

def boundAt (K : Nat) (J : Type v) :=
  renameScope ![1,5,6,(2 : Fin 13)] (CodeUniverseCertificate.query K J)
noncomputable def assignmentAt (K : Nat) (J : Type v) :=
  renameScope ![0,5,6,(3 : Fin 13)] (AssignmentSourceCertificate.query.{u,v} K J)
noncomputable def lookupAt (K : Nat) (J : Type v) :=
  renameScope ![0,5,6,(4 : Fin 13)] (LookupSourceCertificate.query.{u,v} K J)
def tagMap : Fin 12 → Fin 13 := ![0,5,6,0,0,7,8,9,10,11,12,0]
def tagsAt (K : Nat) (J : Type v) :=
  ofConstructibleDeltaZero K J (NaturalTagCertificate.sixTags.rename tagMap)

theorem boundAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (boundAt K J) :=
  (CodeUniverseCertificate.query_isSigmaOne K J).renameScope _
theorem assignmentAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (assignmentAt.{u,v} K J) :=
  (AssignmentSourceCertificate.query_isSigmaOne K J).renameScope _
theorem lookupAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (lookupAt.{u,v} K J) :=
  (LookupSourceCertificate.query_isSigmaOne K J).renameScope _
theorem tagsAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (tagsAt K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

noncomputable def leftBody (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (boundAt K J) (assignmentAt.{u,v} K J)
    (boundAt_isSigmaOne K J) (assignmentAt_isSigmaOne K J)
noncomputable def rightBody (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (lookupAt.{u,v} K J) (tagsAt K J)
    (lookupAt_isSigmaOne K J) (tagsAt_isSigmaOne K J)
noncomputable def query (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (leftBody.{u,v} K J) (rightBody.{u,v} K J)
    (sigmaConjFormula_isSigmaOne _ _ _ _) (sigmaConjFormula_isSigmaOne _ _ _ _)
theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_query {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 13 → A) :
    realize N (query.{u,v} K J) Empty.elim p ↔
      realize N (CodeUniverseCertificate.query K J) Empty.elim ![p 1,p 5,p 6,p 2] ∧
      realize N (AssignmentSourceCertificate.query.{u,v} K J) Empty.elim ![p 0,p 5,p 6,p 3] ∧
      realize N (LookupSourceCertificate.query.{u,v} K J) Empty.elim ![p 0,p 5,p 6,p 4] ∧
      realize N (tagsAt K J) Empty.elim p := by
  unfold query leftBody rightBody
  rw [realize_sigmaConjFormula,realize_sigmaConjFormula,realize_sigmaConjFormula]
  simp only [boundAt,assignmentAt,lookupAt,realize_renameScope]
  have hb : p ∘ ![1,5,6,(2 : Fin 13)] = ![p 1,p 5,p 6,p 2] := by
    funext i; fin_cases i <;> rfl
  have ha : p ∘ ![0,5,6,(3 : Fin 13)] = ![p 0,p 5,p 6,p 3] := by
    funext i; fin_cases i <;> rfl
  have hl : p ∘ ![0,5,6,(4 : Fin 13)] = ![p 0,p 5,p 6,p 4] := by
    funext i; fin_cases i <;> rfl
  rw [hb,ha,hl,and_assoc]

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (κ : Ordinal.{u}) (U : LCarrier.{u})
    (p : Fin 13 → ZFCarrier V) (hU : (p 0).val = U.val) (hκ : (p 1).val = κ.toZFSet)
    (hOmega : (p 5).val = Ordinal.omega0.toZFSet) (hZero : (p 6).val = ∅)
    (h : realize N (query.{u+1,v} K J) Empty.elim p) :
    ∀ i, (p i).val = (fixedParameters κ U i).val := by
  obtain ⟨hb,ha,hl,ht⟩ := (realize_query N p).mp h
  have hB := CodeUniverseCertificate.query_sound hV N hmem ![p 1,p 5,p 6,p 2]
    hOmega hZero (ordinalCarrier κ) hκ hb
  have hA := AssignmentSourceCertificate.query_sound hV N hmem U ![p 0,p 5,p 6,p 3]
    hU hOmega hZero ha
  have hL := LookupSourceCertificate.query_sound hV N hmem U ![p 0,p 5,p 6,p 4]
    hU hOmega hZero hl
  rw [tagsAt,realize_ofConstructibleDeltaZero_absolute hV N hmem,satisfies_rename] at ht
  have hTags := (NaturalTagCertificate.satisfies_sixTags _ hOmega hZero).mp ht
  change (p 7).val = natCode 1 ∧ (p 8).val = natCode 2 ∧ (p 9).val = natCode 3 ∧
    (p 10).val = natCode 4 ∧ (p 11).val = natCode 5 ∧ (p 12).val = natCode 6 at hTags
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hTags
  intro i
  fin_cases i <;> first
    | exact hU | exact hκ | exact hB | exact hA | exact hL | exact hOmega | exact hZero
    | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6

theorem actual_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (p : Fin 13 → ZFCarrier V)
    (hp : ∀ i, (p i).val = (fixedParameters κ U i).val) :
    realize N (query.{u+1,v} K J) Empty.elim p := by
  apply (realize_query N p).mpr
  refine ⟨?_,?_,?_,?_⟩
  · exact (CodeUniverseCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
      ![p 1,p 5,p 6,p 2] (hp 5) (hp 6) (ordinalCarrier κ) (hp 1)).mpr (hp 2)
  · exact (AssignmentSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
      U ![p 0,p 5,p 6,p 3] (hp 0) (hp 5) (hp 6)).mpr (hp 3)
  · exact (LookupSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
      U ![p 0,p 5,p 6,p 4] (hp 0) (hp 5) (hp 6)).mpr (hp 4)
  · rw [tagsAt,realize_ofConstructibleDeltaZero_absolute hV N hmem,satisfies_rename]
    exact (NaturalTagCertificate.satisfies_sixTags _ (hp 5) (hp 6)).mpr
      ⟨hp 7,hp 8,hp 9,hp 10,hp 11,hp 12⟩

end OneYTruth.FixedTowerSources

#print axioms OneYTruth.FixedTowerSources.query_sound
#print axioms OneYTruth.FixedTowerSources.actual_query
