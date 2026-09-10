import OneYTruth.DirectSchemaHelpers

/-! Direct bounded schema checks use the existing complete source sets,
and never ask for a new collection of syntactically rewritten schemas. -/

namespace OneYTruth.DirectSchema

open Constructible Constructible.Delta0Formula

universe u

def Separation (U F A nodes S : ZFSet.{u}) : Prop :=
  ∀ e ∈ F, ∀ p ∈ A, ScopeOne U A nodes e p →
    ∀ a ∈ U, ∃ b ∈ U, ∀ x ∈ U,
      x ∈ b ↔ x ∈ a ∧ ExtendedHolds A S e p x

def separationMatrix : Delta0Formula 10 :=
  .biimp (.mem 9 8) (.conj (.mem 9 7) (extendedHoldsAt 2 4 5 6 9))

theorem satisfies_separationMatrix (s : Tuple ZFSet.{u} 10) :
    Satisfies ZFMem separationMatrix s ↔
      (s 9 ∈ s 8 ↔ s 9 ∈ s 7 ∧ ExtendedHolds (s 2) (s 4) (s 5) (s 6) (s 9)) := by
  simp only [separationMatrix, satisfies_biimp, Satisfies, satisfies_extendedHoldsAt]

/-- Parameters U,syntax,assignments,nodes,Sat; quantified e,p,a,b,x. -/
def separationFormula : Delta0Formula 5 :=
  .boundedAll 1 (.boundedAll 2 (.imp (scopeOneAt 0 2 3 5 6)
    (.boundedAll 0 (.boundedEx 0 (.boundedAll 0 separationMatrix)))))

theorem satisfies_separationFormula (U F A nodes S : ZFSet.{u}) :
    Satisfies ZFMem separationFormula ![U, F, A, nodes, S] ↔ Separation U F A nodes S := by
  simp only [separationFormula, satisfies_boundedAll, satisfies_imp,
    satisfies_scopeOneAt, Satisfies, satisfies_separationMatrix]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, Separation, ZFMem]

def Collection (U F A nodes S : ZFSet.{u}) : Prop :=
  ∀ e ∈ F, ∀ p ∈ A, ScopeTwo U A nodes e p →
    ∀ a ∈ U,
      (∀ x ∈ U, x ∈ a → ∃ y ∈ U, DoubleHolds A S e p x y) →
      ∃ b ∈ U, ∀ x ∈ U, x ∈ a → ∃ y ∈ U, y ∈ b ∧ DoubleHolds A S e p x y

def collectionTotality : Delta0Formula 8 :=
  .boundedAll 0 (.imp (.mem 8 7) (.boundedEx 0 (doubleHoldsAt 2 4 5 6 8 9)))

theorem satisfies_collectionTotality (s : Tuple ZFSet.{u} 8) :
    Satisfies ZFMem collectionTotality s ↔
      ∀ x ∈ s 0, x ∈ s 7 → ∃ y ∈ s 0, DoubleHolds (s 2) (s 4) (s 5) (s 6) x y := by
  simp only [collectionTotality, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_doubleHoldsAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem]

def collectionBound : Delta0Formula 8 :=
  .boundedEx 0 (.boundedAll 0 (.imp (.mem 9 7)
    (.boundedEx 0 (.conj (.mem 10 8) (doubleHoldsAt 2 4 5 6 9 10)))))

theorem satisfies_collectionBound (s : Tuple ZFSet.{u} 8) :
    Satisfies ZFMem collectionBound s ↔
      ∃ b ∈ s 0, ∀ x ∈ s 0, x ∈ s 7 → ∃ y ∈ s 0,
        y ∈ b ∧ DoubleHolds (s 2) (s 4) (s 5) (s 6) x y := by
  simp only [collectionBound, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_doubleHoldsAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem]

def collectionFormula : Delta0Formula 5 :=
  .boundedAll 1 (.boundedAll 2 (.imp (scopeTwoAt 0 2 3 5 6)
    (.boundedAll 0 (.imp collectionTotality collectionBound))))

theorem satisfies_collectionFormula (U F A nodes S : ZFSet.{u}) :
    Satisfies ZFMem collectionFormula ![U, F, A, nodes, S] ↔ Collection U F A nodes S := by
  simp only [collectionFormula, satisfies_boundedAll, satisfies_imp,
    satisfies_scopeTwoAt, Satisfies, satisfies_collectionTotality, satisfies_collectionBound]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, Collection, ZFMem]

def checkFormula : Delta0Formula 5 := .conj separationFormula collectionFormula

theorem satisfies_checkFormula (U F A nodes S : ZFSet.{u}) :
    Satisfies ZFMem checkFormula ![U, F, A, nodes, S] ↔
      Separation U F A nodes S ∧ Collection U F A nodes S := by
  rw [checkFormula]
  exact and_congr (satisfies_separationFormula _ _ _ _ _) (satisfies_collectionFormula _ _ _ _ _)

end OneYTruth.DirectSchema
