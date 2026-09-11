/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookSkolemFunction

/-!
# Finite Skolem-family iteration

This file constructs the omega iteration used in the finite-fragment
reflection proof of Section 6.3 of Wang Fangting, *Axiomatic Set Theory*.
It deliberately stops before calling the result an elementary hull.

An `ExistentialMatrix` packages a formula `phi(params, y)` together with its
parameter arity.  A finite list of these matrices gives the finite family of
Skolem functions.  One pass applies their exact total functions successively;
the stages repeat that pass through omega; and `textbookSkolemOmegaUnion` is
the resulting actual `ZFSet` union.

The present file proves only the structural facts: stages are increasing,
all stages and their union lie in the ambient set, and the original seed lies
in every later construction.  The later closure theorem must still show that
every finite tuple from the omega union occurs together in one stage and then
apply the appropriate function on the next pass.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- A matrix `phi(params, y)` packaged with the arity of `params`. -/
abbrev ExistentialMatrix : Type := Sigma fun n : Nat => FOFormula (n + 1)

/-- An actual `ZFSet` equipped with a proof that it lies inside `U`. -/
abbrev ZFSubset (U : ZFSet.{u}) := {seed : ZFSet.{u} // seed ⊆ U}

/-- Apply one exact total Skolem function while retaining the subset proof. -/
noncomputable def textbookFormulaSkolemStepIn
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrix : ExistentialMatrix) (seed : ZFSubset U) : ZFSubset U :=
  ⟨textbookFormulaSkolemStep seed.1 U seed.2 default matrix.2,
    textbookFormulaSkolemStep_subset seed.2 default matrix.2⟩

@[simp]
theorem textbookFormulaSkolemStepIn_val
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrix : ExistentialMatrix) (seed : ZFSubset U) :
    (textbookFormulaSkolemStepIn U default matrix seed).1 =
      textbookFormulaSkolemStep seed.1 U seed.2 default matrix.2 :=
  rfl

/-- One pass through a finite list of textbook Skolem functions. -/
noncomputable def textbookSkolemPass
    (U : ZFSet.{u}) (default : ZFCarrier U) :
    List ExistentialMatrix -> ZFSubset U -> ZFSubset U
  | [], seed => seed
  | matrix :: rest, seed =>
      textbookSkolemPass U default rest
        (textbookFormulaSkolemStepIn U default matrix seed)

@[simp]
theorem textbookSkolemPass_nil
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U) :
    textbookSkolemPass U default [] seed = seed :=
  rfl

@[simp]
theorem textbookSkolemPass_cons
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrix : ExistentialMatrix) (rest : List ExistentialMatrix)
    (seed : ZFSubset U) :
    textbookSkolemPass U default (matrix :: rest) seed =
      textbookSkolemPass U default rest
        (textbookFormulaSkolemStepIn U default matrix seed) :=
  rfl

/-- A full finite pass retains every member of its input seed. -/
theorem subset_textbookSkolemPass
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    seed.1 ⊆ (textbookSkolemPass U default matrices seed).1 := by
  induction matrices generalizing seed with
  | nil => exact Set.Subset.rfl
  | cons matrix rest ih =>
      exact (seed_subset_textbookFormulaSkolemStep
        seed.2 default matrix.2).trans
          (ih (textbookFormulaSkolemStepIn U default matrix seed))

/-- Every finite pass remains inside its displayed ambient set. -/
theorem textbookSkolemPass_subset
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    (textbookSkolemPass U default matrices seed).1 ⊆ U :=
  (textbookSkolemPass U default matrices seed).2

/-- If a matrix occurs in the finite list, one pass supplies its witness for
every parameter tuple already in the input seed. -/
theorem exists_witnessIn_mem_textbookSkolemPass_of_mem
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    (matrix : ExistentialMatrix) (hmatrix : matrix ∈ matrices)
    (params : Tuple ZFSet.{u} matrix.1)
    (hparams : ∀ i, params i ∈ seed.1)
    (hexists : Model.SatisfiesIn (U : Set ZFSet.{u})
      (.ex matrix.2) params) :
    ∃ y : ZFSet.{u},
      y ∈ (textbookSkolemPass U default matrices seed).1 ∧
        Model.SatisfiesIn (U : Set ZFSet.{u}) matrix.2
          (snoc params y) := by
  induction matrices generalizing seed with
  | nil => simp at hmatrix
  | cons head rest ih =>
      rw [List.mem_cons] at hmatrix
      rcases hmatrix with rfl | hmatrix
      · rcases exists_witnessIn_mem_textbookFormulaSkolemStep
          seed.2 default matrix.2 params hparams hexists with
          ⟨y, hyStep, hySat⟩
        refine ⟨y, ?_, hySat⟩
        exact subset_textbookSkolemPass U default rest
          (textbookFormulaSkolemStepIn U default matrix seed) hyStep
      · refine ih
          (seed := textbookFormulaSkolemStepIn U default head seed)
          hmatrix ?_
        intro i
        exact seed_subset_textbookFormulaSkolemStep
          seed.2 default head.2 (hparams i)

/-- Repeat one finite pass through the natural-number stages. -/
noncomputable def textbookSkolemStage
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    Nat -> ZFSubset U
  | 0 => seed
  | n + 1 => textbookSkolemPass U default matrices
      (textbookSkolemStage U default matrices seed n)

@[simp]
theorem textbookSkolemStage_zero
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    textbookSkolemStage U default matrices seed 0 = seed :=
  rfl

@[simp]
theorem textbookSkolemStage_succ
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) (n : Nat) :
    textbookSkolemStage U default matrices seed (n + 1) =
      textbookSkolemPass U default matrices
        (textbookSkolemStage U default matrices seed n) :=
  rfl

/-- Each stage is contained in its successor. -/
theorem textbookSkolemStage_subset_succ
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) (n : Nat) :
    (textbookSkolemStage U default matrices seed n).1 ⊆
      (textbookSkolemStage U default matrices seed (n + 1)).1 := by
  exact subset_textbookSkolemPass U default matrices
    (textbookSkolemStage U default matrices seed n)

/-- The stage sequence is monotone. -/
theorem textbookSkolemStage_mono
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    {m n : Nat} (hmn : m ≤ n) :
    (textbookSkolemStage U default matrices seed m).1 ⊆
      (textbookSkolemStage U default matrices seed n).1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans
        (textbookSkolemStage_subset_succ U default matrices seed n)

/-- The actual set union of all natural-number stages. -/
noncomputable def textbookSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) : ZFSet.{u} :=
  ZFSet.iUnion fun n : Nat =>
    (textbookSkolemStage U default matrices seed n).1

@[simp]
theorem mem_textbookSkolemOmegaUnion_iff
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    (x : ZFSet.{u}) :
    x ∈ textbookSkolemOmegaUnion U default matrices seed ↔
      ∃ n : Nat, x ∈ (textbookSkolemStage U default matrices seed n).1 := by
  simp [textbookSkolemOmegaUnion]

/-- Every stage is contained in the omega union. -/
theorem textbookSkolemStage_subset_omegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) (n : Nat) :
    (textbookSkolemStage U default matrices seed n).1 ⊆
      textbookSkolemOmegaUnion U default matrices seed := by
  intro x hx
  exact (mem_textbookSkolemOmegaUnion_iff U default matrices seed x).mpr
    ⟨n, hx⟩

/-- The initial seed is contained in the omega union. -/
theorem seed_subset_textbookSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    seed.1 ⊆ textbookSkolemOmegaUnion U default matrices seed := by
  simpa only [textbookSkolemStage_zero] using
    textbookSkolemStage_subset_omegaUnion U default matrices seed 0

/-- The whole omega union remains inside the ambient set. -/
theorem textbookSkolemOmegaUnion_subset
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    textbookSkolemOmegaUnion U default matrices seed ⊆ U := by
  intro x hx
  rcases (mem_textbookSkolemOmegaUnion_iff U default matrices seed x).mp hx with
    ⟨n, hxn⟩
  exact (textbookSkolemStage U default matrices seed n).2 hxn

/-! ## The finite-tuple and Tarski--Vaught closure arguments -/

/-- Every finite tuple from the omega union is already contained in one
common finite stage. -/
theorem exists_textbookSkolemStage_for_tuple
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    {n : Nat} (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈
      textbookSkolemOmegaUnion U default matrices seed) :
    ∃ stage : Nat, ∀ i,
      params i ∈ (textbookSkolemStage U default matrices seed stage).1 := by
  induction n with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let initial : Tuple ZFSet.{u} n := fun i => params i.castSucc
      have hinitial : ∀ i, initial i ∈
          textbookSkolemOmegaUnion U default matrices seed :=
        fun i => hparams i.castSucc
      rcases ih initial hinitial with ⟨initialStage, hinitialStage⟩
      rcases (mem_textbookSkolemOmegaUnion_iff U default matrices seed
        (params (Fin.last n))).mp (hparams (Fin.last n)) with
        ⟨lastStage, hlastStage⟩
      refine ⟨max initialStage lastStage, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact textbookSkolemStage_mono U default matrices seed
          (Nat.le_max_right initialStage lastStage) hlastStage
      · exact textbookSkolemStage_mono U default matrices seed
          (Nat.le_max_left initialStage lastStage) (hinitialStage j)

/-- A listed existential matrix has witnesses over every tuple from the
omega union. -/
theorem exists_witnessIn_mem_textbookSkolemOmegaUnion_of_mem
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    (matrix : ExistentialMatrix) (hmatrix : matrix ∈ matrices)
    (params : Tuple ZFSet.{u} matrix.1)
    (hparams : ∀ i, params i ∈
      textbookSkolemOmegaUnion U default matrices seed)
    (hexists : Model.SatisfiesIn (U : Set ZFSet.{u})
      (.ex matrix.2) params) :
    ∃ y : ZFSet.{u},
      y ∈ textbookSkolemOmegaUnion U default matrices seed ∧
        Model.SatisfiesIn (U : Set ZFSet.{u}) matrix.2
          (snoc params y) := by
  rcases exists_textbookSkolemStage_for_tuple U default matrices seed
      params hparams with ⟨stage, hstage⟩
  rcases exists_witnessIn_mem_textbookSkolemPass_of_mem
      U default matrices
      (textbookSkolemStage U default matrices seed stage)
      matrix hmatrix params hstage hexists with
    ⟨y, hyNext, hySat⟩
  refine ⟨y, ?_, hySat⟩
  exact textbookSkolemStage_subset_omegaUnion U default matrices seed
    (stage + 1) hyNext

/-- The finite list contains a Skolem matrix for every existential
subformula of `formula`. -/
def CoversExistentialSubformulas
    (matrices : List ExistentialMatrix) :
    {n : Nat} -> FOFormula n -> Prop
  | _, .mem _ _ => True
  | _, .eq _ _ => True
  | _, .neg formula => CoversExistentialSubformulas matrices formula
  | _, .conj formula psi =>
      CoversExistentialSubformulas matrices formula ∧
        CoversExistentialSubformulas matrices psi
  | n, .ex matrix =>
      (⟨n, matrix⟩ : ExistentialMatrix) ∈ matrices ∧
        CoversExistentialSubformulas matrices matrix

/-- Enlarging the matrix list preserves coverage of a formula. -/
theorem CoversExistentialSubformulas.mono
    {small big : List ExistentialMatrix}
    (hsubset : ∀ matrix, matrix ∈ small -> matrix ∈ big)
    {n : Nat} {formula : FOFormula n}
    (hcover : CoversExistentialSubformulas small formula) :
    CoversExistentialSubformulas big formula := by
  induction formula with
  | mem i j => trivial
  | eq i j => trivial
  | neg formula ih => exact ih hcover
  | conj formula psi ihFormula ihPsi =>
      exact ⟨ihFormula hcover.1, ihPsi hcover.2⟩
  | @ex m matrix ih =>
      exact ⟨hsubset ⟨m, matrix⟩ hcover.1, ih hcover.2⟩

/-- The finite list of all existential matrices occurring in a formula. -/
def existentialMatrices : {n : Nat} -> FOFormula n -> List ExistentialMatrix
  | _, .mem _ _ => []
  | _, .eq _ _ => []
  | _, .neg formula => existentialMatrices formula
  | _, .conj formula psi =>
      existentialMatrices formula ++ existentialMatrices psi
  | n, .ex matrix =>
      (⟨n, matrix⟩ : ExistentialMatrix) :: existentialMatrices matrix

/-- The recursively generated list really covers every existential
subformula, including nested ones. -/
theorem coversExistentialSubformulas_existentialMatrices
    {n : Nat} (formula : FOFormula n) :
    CoversExistentialSubformulas (existentialMatrices formula) formula := by
  induction formula with
  | mem i j => trivial
  | eq i j => trivial
  | neg formula ih => exact ih
  | conj formula psi ihFormula ihPsi =>
      constructor
      · exact CoversExistentialSubformulas.mono
          (fun _ hmatrix => List.mem_append_left _ hmatrix) ihFormula
      · exact CoversExistentialSubformulas.mono
          (fun _ hmatrix => List.mem_append_right _ hmatrix) ihPsi
  | @ex m matrix ih =>
      exact ⟨List.mem_cons_self, CoversExistentialSubformulas.mono
        (fun _ hitem => List.mem_cons_of_mem _ hitem) ih⟩

/-- A covering finite Skolem family gives the exact recursive witness
closure required for its target formula. -/
theorem closesWithin_textbookSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n)
    (hcover : CoversExistentialSubformulas matrices formula) :
    ClosesWithin
      (textbookSkolemOmegaUnion U default matrices seed : Set ZFSet.{u})
      (U : Set ZFSet.{u}) formula := by
  induction formula with
  | mem i j => trivial
  | eq i j => trivial
  | neg formula ih => exact ih hcover
  | conj formula psi ihFormula ihPsi =>
      exact ⟨ihFormula hcover.1, ihPsi hcover.2⟩
  | @ex m matrix ih =>
      refine ⟨ih hcover.2, ?_⟩
      intro params hparams hexists
      exact exists_witnessIn_mem_textbookSkolemOmegaUnion_of_mem
        U default matrices seed ⟨m, matrix⟩ hcover.1
        params hparams hexists

/-- Satisfaction of every covered formula is absolute between the omega
union and the ambient set for parameters from the union. -/
theorem satisfiesIn_textbookSkolemOmegaUnion_iff
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n)
    (hcover : CoversExistentialSubformulas matrices formula)
    (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈
      textbookSkolemOmegaUnion U default matrices seed) :
    Model.SatisfiesIn
        (textbookSkolemOmegaUnion U default matrices seed : Set ZFSet.{u})
        formula params ↔
      Model.SatisfiesIn (U : Set ZFSet.{u}) formula params := by
  exact satisfiesIn_iff_of_closesWithin
    (textbookSkolemOmegaUnion_subset U default matrices seed)
    formula
    (closesWithin_textbookSkolemOmegaUnion U default matrices seed
      formula hcover)
    params hparams

/-! ## The canonical finite fragment attached to one formula -/

/-- The omega union obtained from exactly the existential subformulas of
`formula`. -/
noncomputable def textbookFormulaSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n) : ZFSet.{u} :=
  textbookSkolemOmegaUnion U default (existentialMatrices formula) seed

/-- The formula-generated omega union contains the original seed. -/
theorem seed_subset_textbookFormulaSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n) :
    seed.1 ⊆ textbookFormulaSkolemOmegaUnion U default seed formula := by
  exact seed_subset_textbookSkolemOmegaUnion U default
    (existentialMatrices formula) seed

/-- The formula-generated omega union remains inside the ambient set. -/
theorem textbookFormulaSkolemOmegaUnion_subset
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n) :
    textbookFormulaSkolemOmegaUnion U default seed formula ⊆ U := by
  exact textbookSkolemOmegaUnion_subset U default
    (existentialMatrices formula) seed

/-- The canonical list of existential subformulas gives recursive witness
closure for the original formula. -/
theorem closesWithin_textbookFormulaSkolemOmegaUnion
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n) :
    ClosesWithin
      (textbookFormulaSkolemOmegaUnion U default seed formula :
        Set ZFSet.{u})
      (U : Set ZFSet.{u}) formula := by
  exact closesWithin_textbookSkolemOmegaUnion U default
    (existentialMatrices formula) seed formula
    (coversExistentialSubformulas_existentialMatrices formula)

/-- Tarski satisfaction for the target formula is absolute between its
canonical finite-fragment omega union and the ambient set. -/
theorem satisfiesIn_textbookFormulaSkolemOmegaUnion_iff
    (U : ZFSet.{u}) (default : ZFCarrier U) (seed : ZFSubset U)
    {n : Nat} (formula : FOFormula n) (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈
      textbookFormulaSkolemOmegaUnion U default seed formula) :
    Model.SatisfiesIn
        (textbookFormulaSkolemOmegaUnion U default seed formula :
          Set ZFSet.{u})
        formula params ↔
      Model.SatisfiesIn (U : Set ZFSet.{u}) formula params := by
  exact satisfiesIn_textbookSkolemOmegaUnion_iff U default
    (existentialMatrices formula) seed formula
    (coversExistentialSubformulas_existentialMatrices formula)
    params hparams

end

end Constructible
