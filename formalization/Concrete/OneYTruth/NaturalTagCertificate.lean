import OneYTruth.EvaluationHistory

/-! Exact bounded checks of the fixed natural constructor tags. Membership
in omega is checked: the weak maximum-element successor test alone would
not characterize a successor among arbitrary sets. -/

namespace OneYTruth.NaturalTagCertificate

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF
open BoundedEvaluation

universe u

def successorAt {n : Nat} (omega previous out : Fin n) : Delta0Formula n :=
  .conj (.mem out omega) (BoundedEvaluation.successorAt out previous)

theorem satisfies_successorAt {n : Nat} (omega previous out : Fin n)
    (p : Fin n → ZFSet.{u}) (hOmega : p omega = Ordinal.omega0.toZFSet)
    (m : Nat) (hm : p previous = natCode m) :
    Satisfies ZFMem (successorAt omega previous out) p ↔ p out = natCode (m + 1) := by
  simp only [successorAt, Satisfies, BoundedEvaluation.satisfies_successorAt, hOmega, hm]
  constructor
  · rintro ⟨hW, hs⟩
    obtain ⟨r, hr⟩ := (mem_omega_iff_exists_natCode _).mp hW
    rw [hr, isSuccessor_natCode_iff] at hs
    exact hr.trans (congrArg natCode hs)
  · intro h
    rw [h]
    exact ⟨(mem_omega_iff_exists_natCode _).mpr ⟨m + 1, rfl⟩,
      (isSuccessor_natCode_iff (m+1) m).mpr rfl⟩

/-- Positions 1 and 2 are omega and zero; positions 5 through 10 are tags. -/
def sixTags : Delta0Formula 12 :=
  .conj (successorAt 1 2 5) (.conj (successorAt 1 5 6)
    (.conj (successorAt 1 6 7) (.conj (successorAt 1 7 8)
      (.conj (successorAt 1 8 9) (successorAt 1 9 10)))))

def SixTags (p : Fin 12 → ZFSet.{u}) : Prop :=
  p 5 = natCode 1 ∧ p 6 = natCode 2 ∧ p 7 = natCode 3 ∧
    p 8 = natCode 4 ∧ p 9 = natCode 5 ∧ p 10 = natCode 6

theorem satisfies_sixTags (p : Fin 12 → ZFSet.{u})
    (hOmega : p 1 = Ordinal.omega0.toZFSet) (hZero : p 2 = ∅) :
    Satisfies ZFMem sixTags p ↔ SixTags p := by
  have h0 : p 2 = natCode 0 := by simpa [natCode] using hZero
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have e1 := (satisfies_successorAt 1 2 5 p hOmega 0 h0).mp h1
    have e2 := (satisfies_successorAt 1 5 6 p hOmega 1 e1).mp h2
    have e3 := (satisfies_successorAt 1 6 7 p hOmega 2 e2).mp h3
    have e4 := (satisfies_successorAt 1 7 8 p hOmega 3 e3).mp h4
    have e5 := (satisfies_successorAt 1 8 9 p hOmega 4 e4).mp h5
    have e6 := (satisfies_successorAt 1 9 10 p hOmega 5 e5).mp h6
    exact ⟨e1, e2, e3, e4, e5, e6⟩
  · rintro ⟨e1, e2, e3, e4, e5, e6⟩
    exact ⟨(satisfies_successorAt 1 2 5 p hOmega 0 h0).mpr e1,
      (satisfies_successorAt 1 5 6 p hOmega 1 e1).mpr e2,
      (satisfies_successorAt 1 6 7 p hOmega 2 e2).mpr e3,
      (satisfies_successorAt 1 7 8 p hOmega 3 e3).mpr e4,
      (satisfies_successorAt 1 8 9 p hOmega 4 e4).mpr e5,
      (satisfies_successorAt 1 9 10 p hOmega 5 e5).mpr e6⟩

end OneYTruth.NaturalTagCertificate

#print axioms OneYTruth.NaturalTagCertificate.satisfies_sixTags
