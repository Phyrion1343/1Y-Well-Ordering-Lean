import OneYTruth.AuxiliarySetTranslation
import OneYTruth.PureFOTranslation

/-!
# A fixed pure formula compiled from a relativized auxiliary formula

The two domain/relation parameters occupy the first two bounded slots.
The remaining slots retain the original assignment order.  Compilation is
purely syntactic, and its correctness holds over every set domain.
-/

namespace OneYTruth.AuxiliaryCode

open Constructible Constructible.Model FirstOrder FirstOrder.Language

universe u v

/-- Move the two free variables to the beginning of the bounded scope. -/
def closeScope {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) n) :
    Language.setTheory.BoundedFormula Empty (2 + n) :=
  BoundedFormula.relabel
    (Sum.elim (fun i : Fin 2 => Sum.inr (i.castAdd n))
      (fun i : Fin n => Sum.inr (i.natAdd 2)))
    φ.toFormula

theorem realize_closeScope {A : Type u} [Language.setTheory.Structure A]
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) n)
    (us : Fin 2 → A) (xs : Fin n → A) :
    (closeScope φ).Realize Empty.elim (Fin.append us xs) ↔ φ.Realize us xs := by
  rw [closeScope, BoundedFormula.realize_relabel]
  have hv : Sum.elim (Empty.elim : Empty → A)
      (Fin.append us xs ∘ Fin.castAdd 0) ∘
      Sum.elim (fun i : Fin 2 => Sum.inr (i.castAdd n))
        (fun i : Fin n => Sum.inr (i.natAdd 2)) = Sum.elim us xs := by
    funext i
    cases i with
    | inl i => exact Fin.append_left us xs i
    | inr i => exact Fin.append_right us xs i
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  rfl

theorem realize_closeScope_snoc {A : Type u} [Language.setTheory.Structure A]
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) (n + 1))
    (us : Fin 2 → A) (xs : Fin n → A) (x : A) :
    (closeScope φ).Realize Empty.elim (Fin.snoc (Fin.append us xs) x) ↔
      φ.Realize us (Fin.snoc xs x) := by
  rw [← Fin.append_snoc]
  exact realize_closeScope φ us (Fin.snoc xs x)

/-- The formula in the pure (`0`, `Empty`) mixed language used by actual Sat. -/
def compile {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) n) :
    (language 0 Empty).BoundedFormula Empty (2 + n) :=
  ofConstructibleFO 0 Empty (fromBoundedFormula (closeScope φ))

theorem realize_compile {A : Type u} (N : Interpretation 0 Empty A)
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) n)
    (us : Fin 2 → A) (xs : Fin n → A) :
    letI : Language.setTheory.Structure A := setTheoryStructure N.mem
    OneYTruth.realize N (compile φ) Empty.elim (Fin.append us xs) ↔
      φ.Realize us xs := by
  letI : Language.setTheory.Structure A := setTheoryStructure N.mem
  rw [compile, realize_ofConstructibleFO]
  exact (realize_fromBoundedFormula N.mem (closeScope φ) (Fin.append us xs)).symm.trans
    (realize_closeScope φ us xs)

theorem realize_compile_snoc {A : Type u} (N : Interpretation 0 Empty A)
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) (n + 1))
    (us : Fin 2 → A) (xs : Fin n → A) (x : A) :
    letI : Language.setTheory.Structure A := setTheoryStructure N.mem
    OneYTruth.realize N (compile φ) Empty.elim (Fin.snoc (Fin.append us xs) x) ↔
      φ.Realize us (Fin.snoc xs x) := by
  rw [← Fin.append_snoc]
  exact realize_compile N φ us (Fin.snoc xs x)

theorem realize_compile_set {D : ZFSet.{u}}
    (N : Interpretation 0 Empty (ZFCarrier D))
    (hmem : ∀ x y, N.mem x y ↔ x.val ∈ y.val)
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) n)
    (us : Fin 2 → ZFCarrier D) (xs : Fin n → ZFCarrier D) :
    letI : Language.setTheory.Structure (ZFCarrier D) :=
      setTheoryStructure (zfCarrierMem D)
    OneYTruth.realize N (compile φ) Empty.elim (Fin.append us xs) ↔
      φ.Realize us xs := by
  have hE : N.mem = zfCarrierMem D := funext fun x => funext fun y => propext (hmem x y)
  have h := realize_compile N φ us xs
  rw [hE] at h
  exact h

theorem realize_compile_set_snoc {D : ZFSet.{u}}
    (N : Interpretation 0 Empty (ZFCarrier D))
    (hmem : ∀ x y, N.mem x y ↔ x.val ∈ y.val)
    {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) (n + 1))
    (us : Fin 2 → ZFCarrier D) (xs : Fin n → ZFCarrier D) (x : ZFCarrier D) :
    letI : Language.setTheory.Structure (ZFCarrier D) :=
      setTheoryStructure (zfCarrierMem D)
    OneYTruth.realize N (compile φ) Empty.elim (Fin.snoc (Fin.append us xs) x) ↔
      φ.Realize us (Fin.snoc xs x) := by
  rw [← Fin.append_snoc]
  exact realize_compile_set N hmem φ us (Fin.snoc xs x)

#print axioms realize_compile_set
#print axioms realize_compile_set_snoc

end OneYTruth.AuxiliaryCode
