/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookAtomicAbsolute

/-!
# Absoluteness of the textbook Boolean set operations

The complementation and intersection clauses in the textbook recursion for
`E(a,n,m)` are operations on actual sets.  This file packages those operations
as total `ZFSet`-valued functions and proves that their extensional graph
formulas are absolute to every transitive set model of ZF.

The complement is relative to the tuple space supplied as its first input:
`relativeDifferenceZF space r = space \ r`.  Both closure proofs use the
model's own Separation axiom.  The ambient `ZFSet.sep` appearing in the proof
is only the extensional description of that internal Separation witness.
-/

@[expose] public section

open Set

universe u

namespace Constructible

/-! ## Actual set-valued operations -/

/-- Relative complement in a specified ambient set. -/
def relativeDifferenceZF (space r : ZFSet.{u}) : ZFSet.{u} :=
  space \ r

/-- Binary intersection as an actual `ZFSet`. -/
def intersectionZF (r t : ZFSet.{u}) : ZFSet.{u} :=
  r ∩ t

@[simp]
theorem mem_relativeDifferenceZF_iff
    {space r x : ZFSet.{u}} :
    x ∈ relativeDifferenceZF space r ↔ x ∈ space ∧ x ∉ r := by
  simp [relativeDifferenceZF]

@[simp]
theorem mem_intersectionZF_iff {r t x : ZFSet.{u}} :
    x ∈ intersectionZF r t ↔ x ∈ r ∧ x ∈ t := by
  simp [intersectionZF]

namespace TextbookDefFormula

/-! ## Pure membership-language graph formulas -/

/-- A candidate belongs to the relative complement of `removed` in `space`. -/
def relativeDifferenceMemberAt {n : Nat}
    (space removed candidate : Fin n) : FOFormula n :=
  .conj (.mem candidate space) (.neg (.mem candidate removed))

/-- A candidate belongs to the intersection of `left` and `right`. -/
def intersectionMemberAt {n : Nat}
    (left right candidate : Fin n) : FOFormula n :=
  .conj (.mem candidate left) (.mem candidate right)

@[simp]
theorem satisfies_relativeDifferenceMemberAt {A : Type u}
    (E : A → A → Prop) {n : Nat}
    (space removed candidate : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (relativeDifferenceMemberAt space removed candidate) s ↔
      E (s candidate) (s space) ∧ ¬E (s candidate) (s removed) := by
  simp [relativeDifferenceMemberAt]

@[simp]
theorem satisfies_intersectionMemberAt {A : Type u}
    (E : A → A → Prop) {n : Nat}
    (left right candidate : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (intersectionMemberAt left right candidate) s ↔
      E (s candidate) (s left) ∧ E (s candidate) (s right) := by
  simp [intersectionMemberAt]

/--
Layout `[space, removed, output]`.  The bound variable is a candidate member.
-/
def relativeDifferenceOutputFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3)))

/-- Layout `[left, right, output]`. -/
def intersectionOutputFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3)))

/-! ## Exact ambient semantics -/

@[simp]
theorem satisfies_relativeDifferenceOutputFormula
    (space removed output : ZFSet.{u}) :
    FOFormula.Satisfies (· ∈ ·) relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      output = relativeDifferenceZF space removed := by
  rw [relativeDifferenceOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_relativeDifferenceMemberAt]
  change
    (∀ x : ZFSet.{u}, x ∈ output ↔ x ∈ space ∧ x ∉ removed) ↔
      output = relativeDifferenceZF space removed
  rw [ZFSet.ext_iff]
  simp only [mem_relativeDifferenceZF_iff]

@[simp]
theorem satisfies_intersectionOutputFormula
    (left right output : ZFSet.{u}) :
    FOFormula.Satisfies (· ∈ ·) intersectionOutputFormula
        ![left, right, output] ↔
      output = intersectionZF left right := by
  rw [intersectionOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_intersectionMemberAt]
  change
    (∀ x : ZFSet.{u}, x ∈ output ↔ x ∈ left ∧ x ∈ right) ↔
      output = intersectionZF left right
  rw [ZFSet.ext_iff]
  simp only [mem_intersectionZF_iff]

end TextbookDefFormula

namespace Model

noncomputable section

private theorem satisfiesIn_booleanAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_booleanBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Closure obtained from the model's Separation axiom -/

theorem relativeDifferenceZF_mem_of_isTransitiveZFModel
    {M space removed : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hspace : space ∈ M) (hremoved : removed ∈ M) :
    relativeDifferenceZF space removed ∈ M := by
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨space, hspace⟩, ⟨removed, hremoved⟩]
  let base : ZFCarrier M := ⟨space, hspace⟩
  let memberFormula : FOFormula 3 :=
    TextbookDefFormula.relativeDifferenceMemberAt
      (0 : Fin 3) (1 : Fin 3) (Fin.last 2)
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel
    hM memberFormula params base
  have hassign (x : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) x = ![space, removed, x] := by
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (base.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) memberFormula
          (snoc (zfCarrierTupleVal params) x)) =
        relativeDifferenceZF space removed := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_relativeDifferenceZF_iff, hassign]
    simp [base, memberFormula,
      TextbookDefFormula.relativeDifferenceMemberAt, SatisfiesIn]
  rw [hsepEq] at hsep
  exact hsep

theorem intersectionZF_mem_of_isTransitiveZFModel
    {M left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M) :
    intersectionZF left right ∈ M := by
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨left, hleft⟩, ⟨right, hright⟩]
  let base : ZFCarrier M := ⟨left, hleft⟩
  let memberFormula : FOFormula 3 :=
    TextbookDefFormula.intersectionMemberAt
      (0 : Fin 3) (1 : Fin 3) (Fin.last 2)
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel
    hM memberFormula params base
  have hassign (x : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) x = ![left, right, x] := by
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (base.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) memberFormula
          (snoc (zfCarrierTupleVal params) x)) =
        intersectionZF left right := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_intersectionZF_iff, hassign]
    simp [base, memberFormula,
      TextbookDefFormula.intersectionMemberAt, SatisfiesIn]
  rw [hsepEq] at hsep
  exact hsep

/-! ## Exact restricted semantics -/

theorem satisfiesIn_relativeDifferenceOutputFormula_components
    {M space removed output : ZFSet.{u}} :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        (x ∈ output ↔ x ∈ relativeDifferenceZF space removed) := by
  rw [TextbookDefFormula.relativeDifferenceOutputFormula,
    satisfiesIn_booleanAll_iff]
  have hassign (x : ZFSet.{u}) :
      snoc ![space, removed, output] x = ![space, removed, output, x] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h x hx
    have hbiimp := (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![space, removed, output] x)).mp (h x hx)
    rw [hassign x] at hbiimp
    simpa [SatisfiesIn,
      TextbookDefFormula.relativeDifferenceMemberAt] using hbiimp
  · intro h x hx
    apply (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![space, removed, output] x)).mpr
    rw [hassign x]
    simpa [SatisfiesIn,
      TextbookDefFormula.relativeDifferenceMemberAt] using h x hx

theorem satisfiesIn_intersectionOutputFormula_components
    {M left right output : ZFSet.{u}} :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        (x ∈ output ↔ x ∈ intersectionZF left right) := by
  rw [TextbookDefFormula.intersectionOutputFormula,
    satisfiesIn_booleanAll_iff]
  have hassign (x : ZFSet.{u}) :
      snoc ![left, right, output] x = ![left, right, output, x] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h x hx
    have hbiimp := (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![left, right, output] x)).mp (h x hx)
    rw [hassign x] at hbiimp
    simpa [SatisfiesIn,
      TextbookDefFormula.intersectionMemberAt] using hbiimp
  · intro h x hx
    apply (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![left, right, output] x)).mpr
    rw [hassign x]
    simpa [SatisfiesIn,
      TextbookDefFormula.intersectionMemberAt] using h x hx

theorem satisfiesIn_relativeDifferenceOutputFormula_iff
    {M space removed output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hspace : space ∈ M) (hremoved : removed ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      output = relativeDifferenceZF space removed := by
  rw [satisfiesIn_relativeDifferenceOutputFormula_components]
  have hresult : relativeDifferenceZF space removed ∈ M :=
    relativeDifferenceZF_mem_of_isTransitiveZFModel
      hM hspace hremoved
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact (h x (hM.1.mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x (hM.1.mem_trans hx hresult)).mpr hx
  · intro h x _hx
    rw [h]

theorem satisfiesIn_intersectionOutputFormula_iff
    {M left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] ↔
      output = intersectionZF left right := by
  rw [satisfiesIn_intersectionOutputFormula_components]
  have hresult : intersectionZF left right ∈ M :=
    intersectionZF_mem_of_isTransitiveZFModel hM hleft hright
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact (h x (hM.1.mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x (hM.1.mem_trans hx hresult)).mpr hx
  · intro h x _hx
    rw [h]

/-! ## Standard `FunctionAbsoluteTo` packages -/

theorem relativeDifferenceZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) Set.univ
      (fun s : Tuple ZFSet.{u} 2 =>
        relativeDifferenceZF (s 0) (s 1))
      TextbookDefFormula.relativeDifferenceOutputFormula := by
  constructor
  · intro s hs _hsDomain
    exact relativeDifferenceZF_mem_of_isTransitiveZFModel
      hM (hs 0) (hs 1)
  · intro s output hs houtput
    have hassign : snoc s output = ![s 0, s 1, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa using
      (satisfiesIn_relativeDifferenceOutputFormula_iff
        hM (hs 0) (hs 1) houtput)

theorem intersectionZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) Set.univ
      (fun s : Tuple ZFSet.{u} 2 => intersectionZF (s 0) (s 1))
      TextbookDefFormula.intersectionOutputFormula := by
  constructor
  · intro s hs _hsDomain
    exact intersectionZF_mem_of_isTransitiveZFModel
      hM (hs 0) (hs 1)
  · intro s output hs houtput
    have hassign : snoc s output = ![s 0, s 1, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa using
      (satisfiesIn_intersectionOutputFormula_iff
        hM (hs 0) (hs 1) houtput)

end

end Model

end Constructible
