import OneYTruth.AuxiliarySetRestriction
import OneYTruth.CollectionReplacement

/-! The bounded-witness formula for actual auxiliary Collection. -/

namespace OneYTruth.Auxiliary

open Constructible FirstOrder FirstOrder.Language

universe u v

def HasCollection {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U)) : Prop :=
  ∀ (n : Nat) (φ : language.BoundedFormula Empty (n + 2))
    (xs : Fin n → ZFCarrier U) (a : ZFCarrier U),
    (∀ x : ZFCarrier U, x.val ∈ a.val → ∃ y : ZFCarrier U,
      realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y)) →
    ∃ b : ZFCarrier U, ∀ x : ZFCarrier U, x.val ∈ a.val →
      ∃ y : ZFCarrier U, y.val ∈ b.val ∧
        realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y)

def collectionIndex (n : Nat) : Fin (n + 2) → Fin (n + 4) :=
  Fin.lastCases (Fin.last (n + 3)) (fun j =>
    Fin.lastCases (Fin.last (n + 2)).castSucc (fun i => i.castSucc.castSucc.castSucc.castSucc) j)

theorem snoc_comp_collectionIndex {A : Type u} {n : Nat}
    (xs : Fin n → A) (a b x y : A) :
    Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y ∘ collectionIndex n =
      Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [collectionIndex]
  · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [collectionIndex]

def collectionQuery {n : Nat} (φ : language.BoundedFormula Empty (n + 2)) :
    language.BoundedFormula Empty (n + 1) :=
  ((BoundedFormula.imp (L := language)
    (.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last n).castSucc.castSucc)])
    (((.rel .mem ![.var (.inr (Fin.last (n + 3))),
      .var (.inr (Fin.last (n + 1)).castSucc.castSucc)]) ⊓
      reindex (collectionIndex n) φ).ex)).all).ex

theorem realize_collectionQuery {A : Type u} (M : Interpretation A) {n : Nat}
    (φ : language.BoundedFormula Empty (n + 2)) (xs : Fin n → A) (a : A) :
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
      realize M (reindex (collectionIndex n) φ) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc, realize_reindex, snoc_comp_collectionIndex]
  rfl

theorem inclusion_snoc {U V : ZFSet.{u}} (h : V ⊆ U) {n : Nat}
    (xs : Fin n → ZFCarrier V) (x : ZFCarrier V) :
    (fun i => inclusion h ((Fin.snoc xs x : Fin (n + 1) → ZFCarrier V) i)) =
      Fin.snoc (fun i => inclusion h (xs i)) (inclusion h x) := Fin.comp_snoc (inclusion h) xs x

theorem inclusion_empty {U V : ZFSet.{u}} (h : V ⊆ U) :
    (fun i : Empty => inclusion h (Empty.elim i : ZFCarrier V)) = Empty.elim := by
  funext i
  nomatch i

theorem realize_restrict_snoc {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (h : V ⊆ U) (he : letI := M.structure; (setSubstructure M V).IsElementary)
    {n : Nat} (φ : language.BoundedFormula Empty (n + 2))
    (xs : Fin n → ZFCarrier V) (x y : ZFCarrier V) :
    realize (restrict M h) φ Empty.elim (Fin.snoc (Fin.snoc xs x) y) ↔
      realize M φ Empty.elim
        (Fin.snoc (Fin.snoc (fun i => inclusion h (xs i)) (inclusion h x)) (inclusion h y)) := by
  rw [realize_restrict M h he, inclusion_empty, inclusion_snoc, inclusion_snoc]

/-- Transitivity handles every element of a; elementarity finds the internal common bound. -/
theorem restrict_hasCollection {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hmem : M.mem = zfCarrierMem U) (h : V ⊆ U) (hV : V.IsTransitive)
    (he : letI := M.structure; (setSubstructure M V).IsElementary)
    (hCol : HasCollection M) : HasCollection (restrict M h) := by
  intro n φ xs a ht
  have htotal : ∀ x : ZFCarrier U, x.val ∈ a.val → ∃ y : ZFCarrier U,
      realize M φ Empty.elim
        (Fin.snoc (Fin.snoc (fun i => inclusion h (xs i)) x) y) := by
    intro x hx
    let xV : ZFCarrier V := ⟨x.val, hV.mem_trans hx a.property⟩
    obtain ⟨y, hy⟩ := ht xV hx
    have hφ := (realize_restrict_snoc M h he φ xs xV y).mp hy
    have heqx : inclusion h xV = x := Subtype.ext rfl
    exact ⟨inclusion h y, by simpa only [heqx] using hφ⟩
  obtain ⟨b, hb⟩ := hCol n φ (fun i => inclusion h (xs i)) (inclusion h a) htotal
  have hquery : realize M (collectionQuery φ) Empty.elim
      (Fin.snoc (fun i => inclusion h (xs i)) (inclusion h a)) := by
    apply (realize_collectionQuery M φ _ _).mpr
    simpa only [hmem, zfCarrierMem, inclusion] using (show ∃ b : ZFCarrier U, ∀ x : ZFCarrier U,
      x.val ∈ a.val → ∃ y : ZFCarrier U, y.val ∈ b.val ∧
        realize M φ Empty.elim (Fin.snoc (Fin.snoc (fun i => inclusion h (xs i)) x) y) from ⟨b, hb⟩)
  have hqueryV : realize (restrict M h) (collectionQuery φ) Empty.elim (Fin.snoc xs a) := by
    apply (realize_restrict M h he (collectionQuery φ) Empty.elim (Fin.snoc xs a)).mpr
    rw [inclusion_empty, inclusion_snoc]
    exact hquery
  have hsmallmem : (restrict M h).mem = zfCarrierMem V := by
    funext x y
    exact congrFun (congrFun hmem (inclusion h x)) (inclusion h y)
  simpa only [hsmallmem, zfCarrierMem] using
    (realize_collectionQuery (restrict M h) φ xs a).mp hqueryV

theorem collection_with_parameters {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hCol : HasCollection M) {α : Type v} [Fintype α] {n : Nat}
    (φ : language.BoundedFormula α (n + 2)) (v : α → ZFCarrier U)
    (xs : Fin n → ZFCarrier U) (a : ZFCarrier U)
    (ht : ∀ x : ZFCarrier U, x.val ∈ a.val → ∃ y : ZFCarrier U,
      realize M φ v (Fin.snoc (Fin.snoc xs x) y)) :
    ∃ b : ZFCarrier U, ∀ x : ZFCarrier U, x.val ∈ a.val →
      ∃ y : ZFCarrier U, y.val ∈ b.val ∧ realize M φ v (Fin.snoc (Fin.snoc xs x) y) := by
  have hc (x y : ZFCarrier U) :
      realize M (closeParameters φ) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.append (v ∘ (Fintype.equivFin α).symm) xs) x) y) ↔
      realize M φ v (Fin.snoc (Fin.snoc xs x) y) := by
    simpa only [Fin.append_snoc] using realize_closeParameters M φ v (Fin.snoc xs x) y
  obtain ⟨b, hb⟩ := hCol (Fintype.card α + n) (closeParameters (n := n + 1) φ)
    (Fin.append (v ∘ (Fintype.equivFin α).symm) xs) a (fun x hx => by
      obtain ⟨y, hy⟩ := ht x hx
      exact ⟨y, (hc x y).mpr hy⟩)
  refine ⟨b, fun x hx => ?_⟩
  obtain ⟨y, hyb, hy⟩ := hb x hx
  exact ⟨y, hyb, (hc x y).mp hy⟩

theorem reduct_hasCollection {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hCol : HasCollection M) {k : Nat} {I : Type v}
    (block : Fin (k + 1) → ZFCarrier U) (index : I → ZFCarrier U) :
    InternalClosure.HasCollection (reduct M block index) := by
  classical
  intro n φ xs a ht
  let v := Sum.elim (Empty.elim : Empty → ZFCarrier U)
    (Sum.elim block (fun i : {i // i ∈ namedSupport φ} => index i.val))
  obtain ⟨b, hb⟩ := collection_with_parameters M hCol (finiteTranslate φ) v xs a (fun x hx => by
    obtain ⟨y, hy⟩ := ht x hx
    exact ⟨y, (realize_finiteTranslate M block index φ Empty.elim _).mpr hy⟩)
  refine ⟨b, fun x hx => ?_⟩
  obtain ⟨y, hyb, hy⟩ := hb x hx
  exact ⟨y, hyb, (realize_finiteTranslate M block index φ Empty.elim _).mp hy⟩

end OneYTruth.Auxiliary
