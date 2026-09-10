import OneYTruth.AuxiliaryCollectionSchema

/-! Actual mixed-language formulas expressing Separation and Collection instances. -/

namespace OneYTruth.SchemaQueries

open FirstOrder FirstOrder.Language Constructible

universe u v

def separationQuery {k : Nat} {I : Type u} {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 1)) :
    (language k I).BoundedFormula Empty (n + 1) :=
  ((BoundedFormula.iff (L := language k I)
    (.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last (n + 1)).castSucc)])
    ((.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last n).castSucc.castSucc)]) ⊓
      reindexScoped (Auxiliary.separationIndex n) φ)).all).ex

theorem realize_separationQuery {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 1)) (xs : Fin n → A) (a : A) :
    realize M (separationQuery φ) Empty.elim (Fin.snoc xs a) ↔
      ∃ b : A, ∀ x : A, M.mem x b ↔ M.mem x a ∧ realize M φ Empty.elim (Fin.snoc xs x) := by
  letI := M.structure
  unfold realize separationQuery
  simp only [BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_inf]
  change (∃ b : A, ∀ x : A, M.mem
    ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last (n + 2)))
    ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last (n + 1)).castSucc) ↔
    M.mem
      ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last (n + 2)))
      ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last n).castSucc.castSucc) ∧
      realize M (reindexScoped (Auxiliary.separationIndex n) φ) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc, realize_reindexScoped,
    Auxiliary.snoc_comp_separationIndex]
  rfl

def collectionQuery {k : Nat} {I : Type u} {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) :
    (language k I).BoundedFormula Empty (n + 1) :=
  ((BoundedFormula.imp (L := language k I)
    (.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last n).castSucc.castSucc)])
    (((.rel .mem ![.var (.inr (Fin.last (n + 3))),
      .var (.inr (Fin.last (n + 1)).castSucc.castSucc)]) ⊓
      reindexScoped (Auxiliary.collectionIndex n) φ).ex)).all).ex

theorem realize_collectionQuery {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) (xs : Fin n → A) (a : A) :
    realize M (collectionQuery φ) Empty.elim (Fin.snoc xs a) ↔
      ∃ b : A, ∀ x : A, M.mem x a → ∃ y : A, M.mem y b ∧
        realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y) := by
  letI := M.structure
  unfold realize collectionQuery
  simp only [BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  change (∃ b : A, ∀ x : A, M.mem
    ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last (n + 2)))
    ((Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → A) (Fin.last n).castSucc.castSucc) →
    ∃ y : A, M.mem
      ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y : Fin (n + 4) → A) (Fin.last (n + 3)))
      ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y : Fin (n + 4) → A)
        (Fin.last (n + 1)).castSucc.castSucc) ∧
      realize M (reindexScoped (Auxiliary.collectionIndex n) φ) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc, realize_reindexScoped,
    Auxiliary.snoc_comp_collectionIndex]
  rfl

def totalityIndex (n : Nat) : Fin (n + 2) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2)) (fun j =>
    Fin.lastCases (Fin.last (n + 1)).castSucc (fun i => i.castSucc.castSucc.castSucc) j)

theorem snoc_comp_totalityIndex {A : Type v} {n : Nat}
    (xs : Fin n → A) (a x y : A) :
    Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y ∘ totalityIndex n =
      Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [totalityIndex]
  · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [totalityIndex]

def totalityQuery {k : Nat} {I : Type u} {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) :
    (language k I).BoundedFormula Empty (n + 1) :=
  boundedAll (.var (.inr (Fin.last n))) (reindexScoped (totalityIndex n) φ).ex

theorem realize_totalityQuery {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) (xs : Fin n → A) (a : A) :
    realize M (totalityQuery φ) Empty.elim (Fin.snoc xs a) ↔
      ∀ x : A, M.mem x a → ∃ y : A,
        realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y) := by
  letI := M.structure
  rw [totalityQuery, realize_boundedAll]
  simp only [realize, BoundedFormula.realize_ex]
  change (∀ x : A, M.mem x ((Fin.snoc xs a : Fin (n + 1) → A) (Fin.last n)) →
    ∃ y : A, realize M (reindexScoped (totalityIndex n) φ) Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y)) ↔ _
  simp only [Fin.snoc_last, realize_reindexScoped, snoc_comp_totalityIndex]
  rfl

def collectionSchema {k : Nat} {I : Type u} {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) :
    (language k I).BoundedFormula Empty (n + 1) :=
  (totalityQuery φ).imp (collectionQuery φ)

theorem hasSeparation_iff_queries {k : Nat} {I : Type u} {U : ZFSet.{v}}
    (M : Interpretation k I (ZFCarrier U)) (hmem : M.mem = zfCarrierMem U) :
    InternalClosure.HasSeparation M ↔
      ∀ n (φ : (language k I).BoundedFormula Empty (n + 1))
        (xs : Fin n → ZFCarrier U) (a : ZFCarrier U),
          realize M (separationQuery φ) Empty.elim (Fin.snoc xs a) := by
  simp only [InternalClosure.HasSeparation, InternalClosure.SeparationInstance,
    realize_separationQuery, hmem, zfCarrierMem]

theorem hasCollection_iff_queries {k : Nat} {I : Type u} {U : ZFSet.{v}}
    (M : Interpretation k I (ZFCarrier U)) (hmem : M.mem = zfCarrierMem U) :
    InternalClosure.HasCollection M ↔
      ∀ n (φ : (language k I).BoundedFormula Empty (n + 2))
        (xs : Fin n → ZFCarrier U) (a : ZFCarrier U),
          realize M (collectionSchema φ) Empty.elim (Fin.snoc xs a) := by
  have hquery n (φ : (language k I).BoundedFormula Empty (n + 2)) xs a :
      realize M (collectionSchema φ) Empty.elim (Fin.snoc xs a) ↔
        ((∀ x, M.mem x a → ∃ y, realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y)) →
          ∃ b, ∀ x, M.mem x a → ∃ y, M.mem y b ∧
            realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y)) := by
    change (realize M (totalityQuery φ) Empty.elim (Fin.snoc xs a) →
      realize M (collectionQuery φ) Empty.elim (Fin.snoc xs a)) ↔ _
    rw [realize_totalityQuery, realize_collectionQuery]
  simp only [InternalClosure.HasCollection, InternalClosure.CollectionInstance,
    hquery, hmem, zfCarrierMem]

end OneYTruth.SchemaQueries
