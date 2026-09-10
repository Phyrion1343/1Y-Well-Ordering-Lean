import OneYTruth.PureBoundedCompiler
import OneYTruth.ScopedConnectives

/-! A genuine pure Sigma-one formula has a native bounded certificate
using a single set bound. Bounds are monotone and are internally supplied
using only finite set operations after actual witnesses are known. -/

namespace OneYTruth.PureSigmaBounded

open Constructible Constructible.Delta0Formula FirstOrder FirstOrder.Language
open InternalProducts

universe u

def swapLast (n : Nat) : Fin ((n+1)+1) → Fin ((n+1)+1) :=
  Fin.lastCases (Fin.last n).castSucc
    (Fin.lastCases (Fin.last (n+1)) (fun i => i.castSucc.castSucc))

theorem snoc_swapLast {A : Type u} {n : Nat} (p : Fin n → A) (B x : A) :
    (fun i => snoc (snoc p B) x (swapLast n i)) = snoc (snoc p x) B := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [swapLast]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [swapLast]
    · simp [swapLast]

def exFormula {n : Nat} (δ : Delta0Formula ((n+1)+1)) : Delta0Formula (n+1) :=
  .boundedEx (Fin.last n) (δ.rename (swapLast n))

theorem satisfies_exFormula {n : Nat} (δ : Delta0Formula ((n+1)+1))
    (p : Fin n → ZFSet.{u}) (B : ZFSet.{u}) :
    Satisfies ZFMem (exFormula δ) (snoc p B) ↔
      ∃ x ∈ B, Satisfies ZFMem δ (snoc (snoc p x) B) := by
  simp only [exFormula,Satisfies,snoc_last,satisfies_rename,snoc_swapLast]

theorem val_snoc {V : ZFSet.{u}} {n : Nat} (p : Fin n → ZFCarrier V) (x : ZFCarrier V) :
    (fun i => ((Fin.snoc p x : Fin (n+1) → ZFCarrier V) i).val) = snoc (fun i => (p i).val) x.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

structure Certificate {n : Nat} (φ : (language 0 Empty).BoundedFormula Empty n) where
  formula : Delta0Formula (n+1)
  sound : ∀ {V : ZFSet.{u}}, V.IsTransitive →
    ∀ (N : Interpretation 0 Empty (ZFCarrier V)), N.mem = zfCarrierMem V →
    ∀ (p : Fin n → ZFCarrier V) (B : ZFCarrier V),
      Satisfies ZFMem formula (snoc (fun i => (p i).val) B.val) →
        realize N φ Empty.elim p
  monotone : ∀ (p : Fin n → ZFSet.{u}) {B C : ZFSet.{u}}, B ⊆ C →
    Satisfies ZFMem formula (snoc p B) → Satisfies ZFMem formula (snoc p C)
  complete : ∀ {V : ZFSet.{u}}, V.IsTransitive →
    (∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V) →
    (∀ a ∈ V, ZFSet.sUnion a ∈ V) → (∅ : ZFSet.{u}) ∈ V →
    ∀ (N : Interpretation 0 Empty (ZFCarrier V)), N.mem = zfCarrierMem V →
    ∀ p : Fin n → ZFCarrier V, realize N φ Empty.elim p →
      ∃ B : ZFCarrier V, Satisfies ZFMem formula (snoc (fun i => (p i).val) B.val)

theorem exists_certificate {n : Nat} {φ : (language 0 Empty).BoundedFormula Empty n}
    (hφ : IsSigmaOne φ) (hn : 0 < n) : Nonempty (Certificate.{u} φ) := by
  induction hφ with
  | @deltaZero n φ hφ =>
      obtain ⟨δ,hδ⟩ := PureBoundedCompiler.exists_native.{u+1} hφ hn
      refine ⟨⟨δ.rename Fin.castSucc,?_,?_,?_⟩⟩
      · intro V hV N hmem p B h
        rw [satisfies_rename] at h
        simp only [snoc_castSucc] at h
        apply (hδ _ N p).mp
        rw [hmem]
        exact (satisfies_absolute hV δ p).mpr h
      · intro p B C _ h
        simpa only [satisfies_rename,snoc_castSucc] using h
      · intro V hV hpair hUnion h0 N hmem p h
        refine ⟨⟨∅,h0⟩,?_⟩
        simp only [satisfies_rename,snoc_castSucc]
        apply (satisfies_absolute hV δ p).mp
        rw [← hmem]
        exact (hδ _ N p).mpr h
  | @ex n φ hφ ih =>
      obtain ⟨c⟩ := ih (Nat.zero_lt_succ n)
      refine ⟨⟨exFormula c.formula,?_,?_,?_⟩⟩
      · intro V hV N hmem p B h
        obtain ⟨x,hx,hc⟩ := (satisfies_exFormula c.formula _ B.val).mp h
        let xV : ZFCarrier V := ⟨x,hV.mem_trans hx B.property⟩
        apply (realize_scoped_ex N φ p).mpr
        refine ⟨xV,c.sound hV N hmem (Fin.snoc p xV) B ?_⟩
        rw [PureSigmaBounded.val_snoc]
        exact hc
      · intro p B C hBC h
        obtain ⟨x,hx,hc⟩ := (satisfies_exFormula c.formula p B).mp h
        exact (satisfies_exFormula c.formula p C).mpr ⟨x,hBC hx,c.monotone (snoc p x) hBC hc⟩
      · intro V hV hpair hUnion h0 N hmem p h
        obtain ⟨x,hx⟩ := (realize_scoped_ex N φ p).mp h
        obtain ⟨B,hB⟩ := c.complete hV hpair hUnion h0 N hmem (Fin.snoc p x) hx
        let C : ZFCarrier V := ⟨insert x.val B.val,insert_mem hV hpair hUnion x.property B.property⟩
        refine ⟨C,(satisfies_exFormula c.formula _ C.val).mpr ⟨x.val,?_,?_⟩⟩
        · change x.val ∈ insert x.val B.val
          simp
        · apply c.monotone (snoc (fun i => (p i).val) x.val)
            (show B.val ⊆ C.val from fun _ hz => by simpa only [C, ZFSet.mem_insert_iff] using Or.inr hz)
          rw [PureSigmaBounded.val_snoc] at hB
          exact hB

noncomputable def certificate {n : Nat} {φ : (language 0 Empty).BoundedFormula Empty n}
    (hφ : IsSigmaOne φ) (hn : 0 < n) : Certificate.{u} φ :=
  Classical.choice (exists_certificate hφ hn)

end OneYTruth.PureSigmaBounded

#print axioms OneYTruth.PureSigmaBounded.exists_certificate
