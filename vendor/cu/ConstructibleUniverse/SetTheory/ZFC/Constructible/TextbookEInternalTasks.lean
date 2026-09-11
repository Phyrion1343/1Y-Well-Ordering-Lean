/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookESkolemClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph

/-!
# The internal task domain for textbook E witnesses

The witness instances used by `ClosesUnderTextbookEWitnesses` are indexed by
a relation code `m` and a positive arity `n + 1`.  This file represents those
indices by the actual constructible set

`omega x (omega \ {0})`.

The first coordinate is the `E` recursion code and the second coordinate is
the positive arity.  Thus a task is the same Kuratowski key
`<m,n+1>` that the recursion defining `E` uses.  The membership theorem below
proves both coverage and unique decoding; external natural numbers occur only
in that correctness statement, not as the purported internal task set.

The final theorem exactly rewrites `ClosesUnderTextbookEWitnesses` as closure
over members of this internal task domain.  It does not claim that the
corresponding witness operation has already been represented by one internal
function graph or collected through omega by Replacement.  In particular,
constructibility of the uniformly varying values
`textbookEZF U (natCode (n + 1)) (natCode m)` remains a separate obligation.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

/-! ## The actual constructible task set -/

/-- The standard internal omega, packaged as an actual member of `L`. -/
def textbookEOmegaLCarrier : LCarrier.{u} :=
  ⟨textbookEOmegaZF, omega_mem_L⟩

/-- The singleton containing the von Neumann zero, packaged in `L`. -/
def textbookEZeroSingletonLCarrier : LCarrier.{u} :=
  pairLCarrier emptyLCarrier emptyLCarrier

/-- The positive standard naturals `omega \ {0}`, constructed by the
rudimentary difference operation inside `L`. -/
def textbookEPositiveOmegaLCarrier : LCarrier.{u} :=
  ⟨Godel.F1 textbookEOmegaLCarrier.1 textbookEZeroSingletonLCarrier.1,
    by
      simpa [Godel.op] using
        (Godel.op_mem_L (i := (1 : Fin 9))
          textbookEOmegaLCarrier.2 textbookEZeroSingletonLCarrier.2)⟩

/-- Internal witness tasks.  The first coordinate is an `E` code and the
second coordinate is its positive arity. -/
def textbookEWitnessTaskDomain : LCarrier.{u} :=
  prodLCarrier textbookEOmegaLCarrier textbookEPositiveOmegaLCarrier

@[simp]
theorem textbookEWitnessTaskDomain_val :
    (textbookEWitnessTaskDomain : LCarrier.{u}).1 =
      ZFSet.prod textbookEOmegaZF textbookEPositiveOmegaLCarrier.1 :=
  rfl

theorem mem_textbookEPositiveOmegaLCarrier_iff (x : ZFSet.{u}) :
    x ∈ (textbookEPositiveOmegaLCarrier : LCarrier.{u}).1 ↔
      ∃ n : Nat, x = natCode (n + 1) := by
  rw [textbookEPositiveOmegaLCarrier, Godel.mem_F1_iff]
  constructor
  · rintro ⟨hxOmega, hxZero⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hxOmega with
      ⟨n, rfl⟩
    cases n with
    | zero =>
        exfalso
        apply hxZero
        let zeroCode : LCarrier.{u} :=
          ⟨natCode 0, natCode_mem_L 0⟩
        change zeroCode.1 ∈ textbookEZeroSingletonLCarrier.1
        rw [textbookEZeroSingletonLCarrier,
          mem_pairLCarrier_iff]
        apply Or.inl
        apply Subtype.ext
        simp only [zeroCode, emptyLCarrier, natCode, Nat.cast_zero,
          Ordinal.toZFSet_zero]
    | succ n =>
        exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    constructor
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (n + 1))).mpr ⟨n + 1, rfl⟩
    · let succCode : LCarrier.{u} :=
        ⟨natCode (n + 1), natCode_mem_L (n + 1)⟩
      change succCode.1 ∉ textbookEZeroSingletonLCarrier.1
      intro hmem
      rcases (mem_pairLCarrier_iff emptyLCarrier emptyLCarrier
          succCode).mp (by
            simpa only [textbookEZeroSingletonLCarrier] using hmem) with
        heq | heq
      · have hcode : (natCode (n + 1) : ZFSet.{u}) = natCode 0 := by
          calc
            natCode (n + 1) = ∅ := congrArg Subtype.val heq
            _ = natCode 0 := by
              simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
        have : n + 1 = 0 := natCode_injective hcode
        omega
      · have hcode : (natCode (n + 1) : ZFSet.{u}) = natCode 0 := by
          calc
            natCode (n + 1) = ∅ := congrArg Subtype.val heq
            _ = natCode 0 := by
              simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
        have : n + 1 = 0 := natCode_injective hcode
        omega

/-- Exact decoding of every member of the internal task domain. -/
theorem mem_textbookEWitnessTaskDomain_iff (task : ZFSet.{u}) :
    task ∈ (textbookEWitnessTaskDomain : LCarrier.{u}).1 ↔
      ∃ code arity : Nat,
        task = ZFSet.pair (natCode code) (natCode (arity + 1)) := by
  rw [textbookEWitnessTaskDomain_val, ZFSet.mem_prod]
  constructor
  · rintro ⟨codeZF, hcode, arityZF, harity, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode codeZF).mp hcode with
      ⟨code, rfl⟩
    rcases (mem_textbookEPositiveOmegaLCarrier_iff arityZF).mp harity with
      ⟨arity, rfl⟩
    exact ⟨code, arity, rfl⟩
  · rintro ⟨code, arity, rfl⟩
    exact ⟨natCode code,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode code)).mpr ⟨code, rfl⟩,
      natCode (arity + 1),
      (mem_textbookEPositiveOmegaLCarrier_iff
        (natCode (arity + 1))).mpr ⟨arity, rfl⟩,
      rfl⟩

/-- The natural-number labels of an internal witness task are unique. -/
theorem textbookEWitnessTask_decode_unique
    {task : ZFSet.{u}} {code arity code' arity' : Nat}
    (h : task = ZFSet.pair (natCode code) (natCode (arity + 1)))
    (h' : task = ZFSet.pair (natCode code') (natCode (arity' + 1))) :
    code = code' ∧ arity = arity' := by
  have hp := ZFSet.pair_inj.mp (h.symm.trans h')
  constructor
  · exact natCode_injective hp.1
  · have hs : arity + 1 = arity' + 1 := natCode_injective hp.2
    omega

/-- Every witness task is, in particular, a genuine key of the recursion
domain `omega x omega`. -/
theorem textbookEWitnessTaskDomain_subset_textbookEDomain :
    ((textbookEWitnessTaskDomain : LCarrier.{u}).1 : Set ZFSet.{u}) ⊆
      TextbookEDomain := by
  intro task htask
  rcases (mem_textbookEWitnessTaskDomain_iff task).mp htask with
    ⟨code, arity, rfl⟩
  apply mem_textbookEDomain_iff.mpr
  exact ⟨natCode code,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode code)).mpr ⟨code, rfl⟩,
    natCode (arity + 1),
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode (arity + 1))).mpr ⟨arity + 1, rfl⟩,
    rfl⟩

/-! ## Exact reduction of the external closure predicate -/

/-- The witness requirement at one decoded internal task. -/
def ClosesUnderTextbookEWitnessAt
    (small : Set ZFSet.{u}) (U : ZFSet.{u})
    (arity code : Nat) : Prop :=
  ∀ (params : Tuple (ZFCarrier U) arity),
    (∀ i, (params i).1 ∈ small) →
      (∃ x : ZFCarrier U,
        textbookTupleGraph (snoc params x) ∈
          textbookEZF U (natCode (arity + 1)) (natCode code)) →
      ∃ x : ZFCarrier U,
        x.1 ∈ small ∧
          textbookTupleGraph (snoc params x) ∈
            textbookEZF U (natCode (arity + 1)) (natCode code)

/-- A task has its unique decoded witness requirement.  The implication
presentation avoids choosing a decoder; uniqueness is proved above. -/
def ClosesUnderTextbookEWitnessTask
    (small : Set ZFSet.{u}) (U task : ZFSet.{u}) : Prop :=
  ∀ (arity code : Nat),
    task = ZFSet.pair (natCode code) (natCode (arity + 1)) →
      ClosesUnderTextbookEWitnessAt small U arity code

/-- Closure under all textbook `E` witnesses is exactly closure at every
member of the internal task set `omega x (omega \ {0})`. -/
theorem closesUnderTextbookEWitnesses_iff_internalTasks
    (small : Set ZFSet.{u}) (U : ZFSet.{u}) :
    ClosesUnderTextbookEWitnesses small U ↔
      ∀ task : ZFSet.{u},
        task ∈ (textbookEWitnessTaskDomain : LCarrier.{u}).1 →
          ClosesUnderTextbookEWitnessTask small U task := by
  constructor
  · intro hclose task htask arity code htaskEq
    exact hclose code
  · intro htasks arity code params hparams hexists
    let task : ZFSet.{u} :=
      ZFSet.pair (natCode code) (natCode (arity + 1))
    have htask : task ∈
        (textbookEWitnessTaskDomain : LCarrier.{u}).1 :=
      (mem_textbookEWitnessTaskDomain_iff task).mpr
        ⟨code, arity, rfl⟩
    have hat := htasks task htask arity code rfl
    exact hat params hparams hexists

end Model

end

end Constructible
