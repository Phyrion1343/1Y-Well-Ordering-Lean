import OneYTruth.PureDefCertificate

/-! A literal bounded Def step, including the empty-domain base case. -/

namespace OneYTruth.PureDefCertificate

open Constructible Constructible.Delta0Formula FirstOrder FirstOrder.Language
open FormulaCode InternalNodes DirectSchema

universe u v

def matchesAt {n : Nat} (U A S e p b : Fin n) : Delta0Formula n :=
  .conj (subsetAt b U) (.boundedAll U (.biimp (.mem (Fin.last n) b.castSucc)
    (extendedHoldsAt A.castSucc S.castSucc e.castSucc p.castSucc (Fin.last n))))

theorem satisfies_matchesAt {n : Nat} (U A S e p b : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (matchesAt U A S e p b) s ↔ Matches (s U) (s A) (s S) (s e) (s p) (s b) := by
  simp only [matchesAt, Satisfies, satisfies_subsetAt, satisfies_boundedAll,
    satisfies_biimp, satisfies_extendedHoldsAt, snoc_last, snoc_castSucc]
  rfl

/-- U,syntax,assignments,nodes,Sat,D; then e,p,b. -/
def coverageFormula : Delta0Formula 6 :=
  .boundedAll 1 (.boundedAll 2 (.imp (scopeOneAt 0 2 3 6 7)
    (.boundedEx 5 (matchesAt 0 2 4 6 7 8))))

/-- U,syntax,assignments,nodes,Sat,D; then b,e,p. -/
def noJunkFormula : Delta0Formula 6 :=
  .boundedAll 5 (.boundedEx 1 (.boundedEx 2
    (.conj (scopeOneAt 0 2 3 7 8) (matchesAt 0 2 4 7 8 6))))

def checkFormula : Delta0Formula 6 := .conj coverageFormula noJunkFormula

theorem satisfies_checkFormula (U F A nodes S D : ZFSet.{u}) :
    Satisfies ZFMem checkFormula ![U, F, A, nodes, S, D] ↔ Check U F A nodes S D := by
  simp only [checkFormula, coverageFormula, noJunkFormula, Satisfies, satisfies_boundedAll,
    satisfies_imp, satisfies_scopeOneAt, satisfies_matchesAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castLT, Check, ZFMem]

def emptyAt {n : Nat} (U : Fin n) : Delta0Formula n :=
  .boundedAll U (.neg (.eq (Fin.last n) (Fin.last n)))

theorem satisfies_emptyAt {n : Nat} (U : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (emptyAt U) s ↔ s U = ∅ := by
  simp only [emptyAt, satisfies_boundedAll, Satisfies]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    exact ⟨fun hx => False.elim (h x hx True.intro), fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
  · rintro h
    rw [h]
    exact fun x hx => False.elim (ZFSet.notMem_empty x hx)

/-- An explicit zero parameter is required; the other six coordinates are unchanged. -/
def formula : Delta0Formula 7 :=
  .disj (.conj (emptyAt 0) (singletonEqAt 5 6))
    (.conj (.neg (emptyAt 0)) (Delta0Formula.rename Fin.castSucc checkFormula))

theorem satisfies_formula (U F A nodes S D : ZFSet.{u}) :
    Satisfies ZFMem formula ![U, F, A, nodes, S, D, ∅] ↔
      (U = ∅ ∧ D = {∅}) ∨ (U ≠ ∅ ∧ Check U F A nodes S D) := by
  simp only [formula, satisfies_disj, Satisfies, satisfies_emptyAt, satisfies_singletonEqAt,
    Delta0Formula.satisfies_rename]
  have he : (fun i : Fin 6 => (![U, F, A, nodes, S, D, ∅] : Fin 7 → ZFSet.{u}) i.castSucc) =
      ![U, F, A, nodes, S, D] := by funext i; fin_cases i <;> rfl
  rw [he, satisfies_checkFormula]
  rfl

theorem satisfies_formula_iff_DefZF {U D : ZFSet.{u}}
    (N : Interpretation 0 Empty (ZFCarrier U)) (hmem : N.mem = zfCarrierMem U) :
    Satisfies ZFMem formula ![U,
      syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}), assignmentCodes U,
      scopedPairs (k := 0) U Empty.elim, satisfactionSet Empty.elim N, D, ∅] ↔
      D = DefZF U := by
  rw [satisfies_formula]
  by_cases hU : U = ∅
  · simp [hU, DefZF_empty]
  · have hne : U.Nonempty := (ZFSet.eq_empty_or_nonempty U).resolve_left hU
    obtain ⟨x, hx⟩ := (ZFSet.nonempty_def U).mp hne
    haveI : Nonempty (ZFCarrier U) := ⟨⟨x, hx⟩⟩
    simpa [hU] using
      (check_iff_eq_DefZF N hmem : Check U
        (syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u})) (assignmentCodes U)
        (scopedPairs (k := 0) U Empty.elim) (satisfactionSet Empty.elim N) D ↔ D = DefZF U)

def mixedFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I formula

theorem mixedFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedFormula k I) := ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_formula_iff_DefZF {U V D : ZFSet.{u}}
    (M : Interpretation 0 Empty (ZFCarrier U)) (hMmem : M.mem = zfCarrierMem U)
    {k : Nat} {I : Type v} (hV : V.IsTransitive)
    (N : Interpretation k I (ZFCarrier V)) (hNmem : N.mem = zfCarrierMem V)
    (p : Fin 7 → ZFCarrier V)
    (hp : ∀ i, (p i).val = ![U,
      syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}), assignmentCodes U,
      scopedPairs (k := 0) U Empty.elim, satisfactionSet Empty.elim M, D, ∅] i) :
    realize N (mixedFormula k I) Empty.elim p ↔ D = DefZF U := by
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute hV N hNmem]
  rw [show Delta0Formula.val p = ![U,
      syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}), assignmentCodes U,
      scopedPairs (k := 0) U Empty.elim, satisfactionSet Empty.elim M, D, ∅] from funext hp]
  exact satisfies_formula_iff_DefZF M hMmem

end OneYTruth.PureDefCertificate

#print axioms OneYTruth.PureDefCertificate.mixedFormula_isDeltaZero
#print axioms OneYTruth.PureDefCertificate.realize_formula_iff_DefZF
