import OneYTruth.InternalIterationUnion
import OneYTruth.InternalCodeUniverse

/-! The actual full finite-code universe, including its initial seed, is
specified by a finite existential prefix over an explicit bounded matrix. -/

namespace OneYTruth.CodeUniverseCertificate

open Constructible Constructible.Delta0Formula Constructible.Model
open FirstOrder FirstOrder.Language InternalClosure InternalProducts
open InternalIteration ConstructibleCodeUniverse

universe u v

def binaryUnionAt {n : Nat} (out A B : Fin n) : Delta0Formula n :=
  .conj (.boundedAll out (.disj (.mem (Fin.last n) A.castSucc) (.mem (Fin.last n) B.castSucc)))
    (.conj (subsetAt A out) (subsetAt B out))

theorem satisfies_binaryUnionAt {n : Nat} (out A B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (binaryUnionAt out A B) s ↔ s out = s A ∪ s B := by
  simp only [binaryUnionAt, Satisfies, satisfies_boundedAll, satisfies_disj, satisfies_subsetAt,
    snoc_last, snoc_castSucc]
  change ((∀ x ∈ s out, x ∈ s A ∨ x ∈ s B) ∧ s A ⊆ s out ∧ s B ⊆ s out) ↔ _
  constructor
  · rintro ⟨h, ha, hb⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_union]
    exact ⟨h x, fun hx => hx.elim (fun hx => ha hx) (fun hx => hb hx)⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hx => ZFSet.mem_union.mp hx,
      fun _ hx => ZFSet.mem_union.mpr (Or.inl hx), fun _ hx => ZFSet.mem_union.mpr (Or.inr hx)⟩

/-- Alphabet, omega, zero, candidate; seed, family, history, component bound. -/
def matrix : Delta0Formula 8 :=
  .conj (binaryUnionAt 4 0 1) (unionMatrixAt pairStepFormula ![2] 4 1 2 3)

theorem satisfies_matrix (A out seed F H B : ZFSet.{u}) :
    Satisfies ZFMem matrix ![A, Ordinal.omega0.toZFSet, ∅, out, seed, F, H, B] ↔
      seed = A ∪ Ordinal.omega0.toZFSet ∧ IsFamilyCertificate pairStep seed F H B ∧
        out = ZFSet.sUnion F := by
  have hstep (S T : ZFSet.{u}) :
      Satisfies ZFMem pairStepFormula (snoc (snoc
        (fun i : Fin 1 => (![A, Ordinal.omega0.toZFSet, ∅, out, seed] : Fin 5 → ZFSet.{u}) (![2] i)) S) T) ↔
      T = pairStep S := by
    have he : snoc (snoc
        (fun i : Fin 1 => (![A, Ordinal.omega0.toZFSet, ∅, out, seed] : Fin 5 → ZFSet.{u}) (![2] i)) S) T =
        ![∅, S, T] := by funext i; fin_cases i <;> rfl
    rw [he]
    exact satisfies_pairStepFormula ∅ S T
  have hh := satisfies_unionMatrixAt pairStepFormula ![2] 4 1 2 3
    ![A, Ordinal.omega0.toZFSet, ∅, out, seed] rfl rfl pairStep hstep F H B
  have he : snoc (snoc (snoc ![A, Ordinal.omega0.toZFSet, ∅, out, seed] F) H) B =
      ![A, Ordinal.omega0.toZFSet, ∅, out, seed, F, H, B] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hh
  change (Satisfies ZFMem (binaryUnionAt 4 0 1) _ ∧
    Satisfies ZFMem (unionMatrixAt pairStepFormula ![2] 4 1 2 3) _) ↔ _
  rw [satisfies_binaryUnionAt]
  exact and_congr Iff.rfl hh

attribute [irreducible] matrix

def query (k : Nat) (I : Type v) := (ofConstructibleDeltaZero k I matrix).ex.ex.ex.ex

theorem query_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (query k I) :=
  .ex (.ex (.ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)))))

theorem realize_query {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 4 → ZFCarrier V)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅) :
    OneYTruth.realize N (query k I) Empty.elim p ↔
      ∃ S F H B : ZFCarrier V, S.val = (p 0).val ∪ Ordinal.omega0.toZFSet ∧
        IsFamilyCertificate pairStep S.val F.val H.val B.val ∧ (p 3).val = ZFSet.sUnion F.val := by
  have hc (S F H B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero k I matrix) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc p S) F) H) B) ↔
      S.val = (p 0).val ∪ Ordinal.omega0.toZFSet ∧
        IsFamilyCertificate pairStep S.val F.val H.val B.val ∧ (p 3).val = ZFSet.sUnion F.val := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    have he : Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc p S) F) H) B) =
        ![(p 0).val, Ordinal.omega0.toZFSet, ∅, (p 3).val, S.val, F.val, H.val, B.val] := by
      funext i
      fin_cases i <;> simp [Constructible.Delta0Formula.val, Fin.snoc, Fin.castLT, hOmega, hZero]
    rw [he]
    exact satisfies_matrix _ _ _ _ _ _
  letI := N.structure
  change (ofConstructibleDeltaZero k I _).ex.ex.ex.ex.Realize Empty.elim p ↔ _
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro S
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro F
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro H
  rw [BoundedFormula.realize_ex]
  exact exists_congr (hc S F H)

theorem union_pairStep_eq_codeUniverse (A : LCarrier.{u}) :
    ZFSet.sUnion (InternalIteration.family pairStep (A.val ∪ Ordinal.omega0.toZFSet)) =
      (codeUniverse A).val :=
  union_eq_uniform pairStepFormula.toFO ![emptyLCarrier] pairStep pairStepL (fun _ => rfl)
    (ConstructibleCodeUniverse.seed A) pairStep_defines

theorem query_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 4 → ZFCarrier V)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅)
    (A : LCarrier.{u}) (hA : (p 0).val = A.val)
    (hq : OneYTruth.realize N (query k I) Empty.elim p) :
    (p 3).val = (codeUniverse A).val := by
  obtain ⟨S, F, H, B, hS, hF, hout⟩ := (realize_query hV N hmem p hOmega hZero).mp hq
  rw [hA] at hS
  rw [hout, hF.family_eq, hS, union_pairStep_eq_codeUniverse]

theorem realize_query_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (p : Fin 4 → ZFCarrier V) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (A : LCarrier.{u}) (hA : (p 0).val = A.val) :
    OneYTruth.realize N (query k I) Empty.elim p ↔ (p 3).val = (codeUniverse A).val := by
  constructor
  · exact query_sound hV N hmem p hOmega hZero A hA
  · intro hout
    have hW : Ordinal.omega0.toZFSet ∈ V := hOmega ▸ (p 1).property
    have hseed : A.val ∪ Ordinal.omega0.toZFSet ∈ V :=
      binaryUnion_mem hV hpair hUnion (hA ▸ (p 0).property) hW
    have hstep (S T : ZFSet.{u}) :
        Satisfies ZFMem pairStepFormula (snoc (snoc
          (fun i => ((![⟨∅, hempty⟩] : Fin 1 → ZFCarrier V) i).val) S) T) ↔ T = pairStep S := by
      have he : snoc (snoc (fun i => ((![⟨∅, hempty⟩] : Fin 1 → ZFCarrier V) i).val) S) T =
          ![∅, S, T] := by funext i; fin_cases i <;> rfl
      rw [he]
      exact satisfies_pairStepFormula ∅ S T
    have hclosed (S : ZFSet.{u}) (hS : S ∈ V) : pairStep S ∈ V :=
      insert_mem hV hpair hUnion hempty (binaryUnion_mem hV hpair hUnion hS
        (InternalCodeUniverse.F2_mem hV N hmem hCol hSep hpair hUnion hS hS))
    obtain ⟨F, H, B, hF⟩ := exists_internal_familyCertificate hV N hmem hCol hSep hpair hUnion
      hempty hW pairStepFormula ![⟨∅, hempty⟩] pairStep hstep hclosed hseed
    apply (realize_query hV N hmem p hOmega hZero).mpr
    refine ⟨⟨_, hseed⟩, F, H, B, ?_, hF, ?_⟩
    · rw [hA]
    · rw [hF.family_eq, union_pairStep_eq_codeUniverse]
      exact hout

end OneYTruth.CodeUniverseCertificate
