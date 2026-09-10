import OneYTruth.ConstructibleDiagramSources
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0GodelGraph

/-! Literal bounded graphs of products and Separation, for canonical data certificates. -/

namespace OneYTruth.BoundedFilterGraph

open Constructible Constructible.Delta0Formula
open Constructible.Godel
open InternalProducts ConstructibleDiagramSources

universe u v

def filterIndex (n : Nat) : Fin (n + 1) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc)

theorem snoc_filterIndex {A : Type u} {n : Nat} (p : Fin n → A) (a b x : A) :
    (fun i => snoc (snoc (snoc p a) b) x (filterIndex n i)) = snoc p x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [filterIndex]

/-- n fixed parameters, source A, proposed filtered set B. -/
def filterFormula {n : Nat} (φ : Delta0Formula (n + 1)) : Delta0Formula (n + 2) :=
  .conj (subsetAt (Fin.last (n + 1)) (Fin.last n).castSucc)
    (.boundedAll (Fin.last n).castSucc
      (.biimp (.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc)
        (Delta0Formula.rename (filterIndex n) φ)))

theorem satisfies_filterFormula {n : Nat} (φ : Delta0Formula (n + 1))
    (p : Fin n → ZFSet.{u}) (A B : ZFSet.{u}) :
    Satisfies ZFMem (filterFormula φ) (snoc (snoc p A) B) ↔
      B = ZFSet.sep (fun x => Satisfies ZFMem φ (snoc p x)) A := by
  simp only [filterFormula, Satisfies, satisfies_subsetAt, satisfies_boundedAll,
    satisfies_biimp, Delta0Formula.satisfies_rename, snoc_last, snoc_castSucc, snoc_filterIndex]
  change (B ⊆ A ∧ ∀ x ∈ A, x ∈ B ↔ Satisfies ZFMem φ (snoc p x)) ↔ _
  constructor
  · rintro ⟨hsub, h⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    exact ⟨fun hx => ⟨hsub hx, (h x (hsub hx)).mp hx⟩,
      fun hx => (h x hx.1).mpr hx.2⟩
  · rintro rfl
    exact ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1,
      fun x hx => by simp only [ZFSet.mem_sep, hx, true_and]⟩

theorem filtered_range_eq_sep {T : Type v} [Small.{u} T] {n : Nat}
    (code : T → ZFSet.{u}) (P : T → Prop) (φ : Delta0Formula (n + 1))
    (p : Fin n → ZFSet.{u})
    (hφ : ∀ t, Satisfies ZFMem φ (snoc p (code t)) ↔ P t) :
    ZFSet.range (fun t : {t : T // P t} => code t.val) =
      ZFSet.sep (fun x => Satisfies ZFMem φ (snoc p x)) (ZFSet.range code) := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · rintro hx
    obtain ⟨⟨t, ht⟩, rfl⟩ := ZFSet.mem_range.mp hx
    exact ⟨ZFSet.mem_range_self t, (hφ t).mpr ht⟩
  · rintro ⟨hx, ht⟩
    obtain ⟨t, rfl⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range_self (f := fun t : {t : T // P t} => code t.val)
      ⟨t, (hφ t).mp ht⟩

def filterAt {n m : Nat} (φ : Delta0Formula (n + 1))
    (params : Fin n → Fin m) (A B : Fin m) : Delta0Formula m :=
  Delta0Formula.rename (snoc (snoc params A) B) (filterFormula φ)

theorem satisfies_filterAt {n m : Nat} (φ : Delta0Formula (n + 1))
    (params : Fin n → Fin m) (A B : Fin m) (s : Tuple ZFSet.{u} m) :
    Satisfies ZFMem (filterAt φ params A B) s ↔
      s B = ZFSet.sep (fun x => Satisfies ZFMem φ (snoc (fun i => s (params i)) x)) (s A) := by
  rw [filterAt, Delta0Formula.satisfies_rename]
  have h : (fun i => s (snoc (snoc params A) B i)) =
      snoc (snoc (fun i => s (params i)) (s A)) (s B) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
  rw [h, satisfies_filterFormula]

def productAt {n : Nat} (out A B : Fin n) : Delta0Formula n :=
  Delta0Formula.rename ![out, A, B] graphF2Formula

theorem satisfies_productAt {n : Nat} (out A B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (productAt out A B) s ↔ s out = pairProduct (s A) (s B) := by
  rw [productAt, Delta0Formula.satisfies_rename]
  have h : (fun i : Fin 3 => s (![out, A, B] i)) = ![s out, s A, s B] := by
    funext i
    fin_cases i <;> rfl
  rw [h, satisfies_graphF2Formula, pairProduct_eq_F2]

end OneYTruth.BoundedFilterGraph
