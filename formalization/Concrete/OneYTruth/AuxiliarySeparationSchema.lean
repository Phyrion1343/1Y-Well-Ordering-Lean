import OneYTruth.AuxiliaryClosure
import OneYTruth.AuxiliaryElementary

/-! The actual auxiliary Separation scheme transfers by elementarity. -/

namespace OneYTruth.Auxiliary

open Constructible FirstOrder FirstOrder.Language

universe u v

def reindex {n m : Nat} (f : Fin n → Fin m)
    (φ : language.BoundedFormula Empty n) : language.BoundedFormula Empty m :=
  BoundedFormula.relabel (Sum.elim Empty.elim (fun i => Sum.inr (f i))) φ.toFormula

theorem realize_reindex {A : Type u} (M : Interpretation A) {n m : Nat}
    (f : Fin n → Fin m) (φ : language.BoundedFormula Empty n) (xs : Fin m → A) :
    realize M (reindex f φ) Empty.elim xs ↔ realize M φ Empty.elim (xs ∘ f) := by
  letI := M.structure
  unfold realize reindex
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Empty.elim : Empty → A) (xs ∘ Fin.castAdd 0) ∘
      Sum.elim Empty.elim (fun i => Sum.inr (f i)) = Sum.elim Empty.elim (xs ∘ f) := by
    funext i
    cases i with
    | inl e => nomatch e
    | inr i => rfl
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  rfl

def separationIndex (n : Nat) : Fin (n + 1) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc)

theorem snoc_comp_separationIndex {A : Type u} {n : Nat}
    (xs : Fin n → A) (a b x : A) :
    Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x ∘ separationIndex n = Fin.snoc xs x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [separationIndex]

def separationQuery {n : Nat} (φ : language.BoundedFormula Empty (n + 1)) :
    language.BoundedFormula Empty (n + 1) :=
  ((BoundedFormula.iff (L := language)
    (.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last (n + 1)).castSucc)])
    ((.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last n).castSucc.castSucc)]) ⊓
      reindex (separationIndex n) φ)).all).ex

theorem realize_separationQuery {A : Type u} (M : Interpretation A) {n : Nat}
    (φ : language.BoundedFormula Empty (n + 1)) (xs : Fin n → A) (a : A) :
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
      realize M (reindex (separationIndex n) φ) Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc, realize_reindex, snoc_comp_separationIndex]
  rfl

/-- A scheme in an arbitrary membership interpretation; this is genuine formula Separation. -/
def HasRelSeparation {A : Type u} (M : Interpretation A) : Prop :=
  ∀ (n : Nat) (φ : language.BoundedFormula Empty (n + 1)) (xs : Fin n → A) (a : A),
    ∃ b : A, ∀ x : A, M.mem x b ↔ M.mem x a ∧ realize M φ Empty.elim (Fin.snoc xs x)

theorem hasRelSeparation_iff {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hmem : M.mem = zfCarrierMem U) : HasRelSeparation M ↔ HasSeparation M := by
  simp only [HasRelSeparation, HasSeparation, hmem, zfCarrierMem]

theorem onSet_hasRelSeparation {A : Type u} (M : Interpretation A)
    (hSep : HasRelSeparation M) (S : @language.ElementarySubstructure A M.structure) :
    HasRelSeparation (onSet M (S : Set A)) := by
  intro n φ xs a
  apply (realize_separationQuery (onSet M (S : Set A)) φ xs a).mp
  apply (realize_onSet M S (separationQuery φ) Empty.elim (Fin.snoc xs a)).mpr
  have hv : (fun i => (Empty.elim i : S).val) = (Empty.elim : Empty → A) := by
    funext i
    nomatch i
  have hx : (fun i => ((Fin.snoc xs a : Fin (n + 1) → S) i).val) =
      Fin.snoc (fun i => (xs i).val) a.val := Fin.comp_snoc Subtype.val xs a
  rw [hv, hx, realize_separationQuery]
  exact hSep n φ (fun i => (xs i).val) a.val

end OneYTruth.Auxiliary
