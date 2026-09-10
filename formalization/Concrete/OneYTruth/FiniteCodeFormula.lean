import OneYTruth.ConstructibleCodeUniverse

/-!
# Exact bounded formulas for finite code constructors

These formulas check the entire fixed-length pair chain, including its final
empty tail. Constructor tags alone would not reject malformed codes.
-/

namespace OneYTruth.FiniteCodeFormula

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF CodedPaths

universe u

def chainCode (tail : ZFSet.{u}) (xs : List ZFSet.{u}) : ZFSet.{u} :=
  xs.foldr ZFSet.pair tail

theorem chainCode_empty (xs : List ZFSet.{u}) : chainCode ∅ xs = listCode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (ZFSet.pair a) ih

/-- A complete pair chain with m displayed fields and a displayed final tail. -/
def chainEqAt : (m : Nat) → {n : Nat} → (Fin m → Fin n) → Fin n → Fin n → Delta0Formula n
  | 0, _, _, p, tail => .eq p tail
  | m + 1, n, fields, p, tail =>
    .boundedEx p (.boundedEx (Fin.last n)
      (.conj (kuratowskiPairEqAt p.castSucc.castSucc
        (fields 0).castSucc.castSucc (Fin.last (n + 1)))
        (chainEqAt m (fun i => (fields i.succ).castSucc.castSucc)
          (Fin.last (n + 1)) tail.castSucc.castSucc)))

theorem satisfies_chainEqAt (m : Nat) {n : Nat} (fields : Fin m → Fin n) (p tail : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (chainEqAt m fields p tail) s ↔
      s p = chainCode (s tail) (List.ofFn (fun i => s (fields i))) := by
  induction m generalizing n with
  | zero => simp [chainEqAt, Satisfies, chainCode]
  | succ m ih =>
    simp only [chainEqAt, Satisfies, satisfies_kuratowskiPairEqAt, ih,
      snoc_last, snoc_castSucc]
    rw [List.ofFn_succ]
    change (∃ box ∈ s p, ∃ q ∈ box, s p = ZFSet.pair (s (fields 0)) q ∧
      q = chainCode (s tail) (List.ofFn (fun i => s (fields i.succ)))) ↔
        s p = ZFSet.pair (s (fields 0))
          (chainCode (s tail) (List.ofFn (fun i => s (fields i.succ))))
    constructor
    · rintro ⟨box, _, q, _, hp, hq⟩
      exact hp.trans (congrArg (ZFSet.pair (s (fields 0))) hq)
    · intro hp
      let q := chainCode (s tail) (List.ofFn (fun i => s (fields i.succ)))
      refine ⟨{s (fields 0), q}, ?_, q, by simp, hp, rfl⟩
      rw [hp]
      simp [ZFSet.pair, q]

/-- Exact linked-list coding with a separately supplied zero coordinate. -/
theorem satisfies_chainEqAt_empty (m : Nat) {n : Nat} (fields : Fin m → Fin n)
    (p zero : Fin n) (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) :
    Satisfies ZFMem (chainEqAt m fields p zero) s ↔
      s p = listCode (List.ofFn (fun i => s (fields i))) := by
  rw [satisfies_chainEqAt, hzero, chainCode_empty]

/-- The length coordinate is checked separately from all the payload fields. -/
def sequenceEqAt {n : Nat} (m : Nat) (fields : Fin m → Fin n)
    (p length zero : Fin n) : Delta0Formula n :=
  .boundedEx p (.boundedEx (Fin.last n)
    (.conj (kuratowskiPairEqAt p.castSucc.castSucc length.castSucc.castSucc (Fin.last (n + 1)))
      (chainEqAt m (fun i => (fields i).castSucc.castSucc)
        (Fin.last (n + 1)) zero.castSucc.castSucc)))

theorem satisfies_sequenceEqAt_chain {n : Nat} (m : Nat) (fields : Fin m → Fin n)
    (p length zero : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (sequenceEqAt m fields p length zero) s ↔
      s p = ZFSet.pair (s length) (chainCode (s zero) (List.ofFn (fun i => s (fields i)))) := by
  simp only [sequenceEqAt, Satisfies, satisfies_kuratowskiPairEqAt,
    satisfies_chainEqAt, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨box, _, q, _, hp, hq⟩
    exact hp.trans (congrArg (ZFSet.pair (s length)) hq)
  · intro hp
    let q := chainCode (s zero) (List.ofFn (fun i => s (fields i)))
    refine ⟨{s length, q}, ?_, q, by simp, hp, rfl⟩
    rw [hp]
    simp [ZFSet.pair, q]

theorem satisfies_sequenceEqAt {n : Nat} (m : Nat) (fields : Fin m → Fin n)
    (p length zero : Fin n) (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) :
    Satisfies ZFMem (sequenceEqAt m fields p length zero) s ↔
      s p = ZFSet.pair (s length) (listCode (List.ofFn (fun i => s (fields i)))) := by
  simp only [sequenceEqAt, Satisfies, satisfies_kuratowskiPairEqAt,
    satisfies_chainEqAt, snoc_last, snoc_castSucc, hzero, chainCode_empty]
  constructor
  · rintro ⟨box, _, q, _, hp, hq⟩
    exact hp.trans (congrArg (ZFSet.pair (s length)) hq)
  · intro hp
    let q := listCode (List.ofFn (fun i => s (fields i)))
    refine ⟨{s length, q}, ?_, q, by simp, hp, rfl⟩
    rw [hp]
    simp [ZFSet.pair, q]

theorem satisfies_sequenceEqAt_natCode {n : Nat} (m : Nat) (fields : Fin m → Fin n)
    (p length zero : Fin n) (s : Tuple ZFSet.{u} n)
    (hzero : s zero = ∅) (hlength : s length = natCode m) :
    Satisfies ZFMem (sequenceEqAt m fields p length zero) s ↔
      s p = sequenceCode (List.ofFn (fun i => s (fields i))) := by
  rw [satisfies_sequenceEqAt _ _ _ _ _ _ hzero, hlength]
  simp only [sequenceCode, List.length_ofFn]

end OneYTruth.FiniteCodeFormula
