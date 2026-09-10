import OneYTruth.ScopedExistentialBlock
import OneYTruth.InternalFiniteRanges

/-! Literal bounded existential blocks for collecting all local certificates
under one set bound. The block has an exact finite-tuple semantics. -/

namespace OneYTruth.BoundedExistentialBlock

open Constructible Constructible.Delta0Formula

universe u

def bind (n : Nat) : (m : Nat) → Fin n → Delta0Formula (n+m) → Delta0Formula n
  | 0, _, φ => φ
  | m+1, b, φ => bind n m b (.boundedEx (Fin.castAdd m b) φ)

theorem satisfies_bind (n m : Nat) (b : Fin n) (φ : Delta0Formula (n+m))
    (p : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (bind n m b φ) p ↔
      ∃ w : Tuple ZFSet.{u} m, (∀ i, w i ∈ p b) ∧
        Satisfies ZFMem φ (Fin.append p w) := by
  induction m with
  | zero =>
    simp only [bind]
    constructor
    · intro h
      exact ⟨Fin.elim0,fun i => Fin.elim0 i,by simpa [Fin.append_elim0] using h⟩
    · rintro ⟨w,_,h⟩
      have hw : w = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simpa [hw,Fin.append_elim0] using h
  | succ m ih =>
    rw [bind,ih]
    change (∃ w : Tuple ZFSet.{u} m, (∀ i, w i ∈ p b) ∧
      ∃ a ∈ Fin.append p w (Fin.castAdd m b), Satisfies ZFMem φ (snoc (Fin.append p w) a)) ↔ _
    simp only [Fin.append_left,constructible_snoc_eq]
    constructor
    · rintro ⟨w,hw,a,ha,hφ⟩
      refine ⟨Fin.snoc w a,?_,?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using ha
        · simpa only [Fin.snoc_castSucc] using hw j
      · rw [Fin.append_snoc]
        exact hφ
    · rintro ⟨w,hw,hφ⟩
      refine ⟨Fin.init w,fun i => hw i.castSucc,w (Fin.last m),hw (Fin.last m),?_⟩
      rw [← Fin.append_snoc,Fin.snoc_init_self]
      exact hφ

/-- Insert the witness-bound parameter before the finite witness tuple. -/
def insertBound (n m : Nat) : Fin (n+m) → Fin ((n+1)+m) :=
  Fin.addCases (fun i => Fin.castAdd m i.castSucc) (fun j => Fin.natAdd (n+1) j)

theorem append_insertBound (n m : Nat) {A : Type u} (p : Fin n → A)
    (B : A) (w : Fin m → A) :
    (fun i => Fin.append (Fin.snoc p B) w (insertBound n m i)) = Fin.append p w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [insertBound,Fin.addCases_left,Fin.append_left,Fin.snoc_castSucc]
  · simp only [insertBound,Fin.addCases_right,Fin.append_right]

def certificate {n : Nat} (m : Nat) (φ : Delta0Formula (n+m)) : Delta0Formula (n+1) :=
  bind (n+1) m (Fin.last n) (φ.rename (insertBound n m))

theorem satisfies_certificate {n : Nat} (m : Nat) (φ : Delta0Formula (n+m))
    (p : Tuple ZFSet.{u} n) (B : ZFSet.{u}) :
    Satisfies ZFMem (certificate m φ) (snoc p B) ↔
      ∃ w : Tuple ZFSet.{u} m, (∀ i, w i ∈ B) ∧ Satisfies ZFMem φ (Fin.append p w) := by
  rw [certificate,satisfies_bind]
  simp only [snoc_last,satisfies_rename,constructible_snoc_eq,append_insertBound]

end OneYTruth.BoundedExistentialBlock
