/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalPower
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeArithmetic
public import Mathlib.Data.Fin.VecNotation

/-!
# The object-language graph of the textbook enumeration code

Wang's enumeration of the five clauses defining `E` uses the natural number

`2 ^ i * 3 ^ j * 5 ^ tag`.

This file represents that operation in the pure language of membership.  The
formula does not use Lean multiplication or exponentiation: it first defines
the literals `2`, `3`, and `5`, invokes the previously constructed
object-language exponentiation graph three times, and invokes the
object-language multiplication graph twice.  Lean arithmetic occurs only in
the metatheoretic statement of the exact semantics and in canonical witnesses.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

private theorem satisfiesIn_rename_iff_eCode
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    Model.SatisfiesIn M (FOFormula.rename rename formula) s <->
      Model.SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, Model.SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-! ## The pure membership-language formula -/

def textbookECodeFinalFormula : FOFormula 12 :=
  .conj
    (natMulFormulaAt
      (0 : Fin 12) (8 : Fin 12) (9 : Fin 12) (11 : Fin 12))
    (natMulFormulaAt
      (0 : Fin 12) (11 : Fin 12) (10 : Fin 12) (4 : Fin 12))

def textbookECodeAfterPowFiveFormula : FOFormula 11 :=
  .ex textbookECodeFinalFormula

def textbookECodeAfterPowThreeFormula : FOFormula 10 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 11) (7 : Fin 11) (3 : Fin 11) (10 : Fin 11))
    textbookECodeAfterPowFiveFormula

def textbookECodeAfterPowTwoFormula : FOFormula 9 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 10) (6 : Fin 10) (2 : Fin 10) (9 : Fin 10))
    textbookECodeAfterPowThreeFormula

def textbookECodeAfterFiveFormula : FOFormula 8 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 9) (5 : Fin 9) (1 : Fin 9) (8 : Fin 9))
    textbookECodeAfterPowTwoFormula

def textbookECodeAfterThreeFormula : FOFormula 7 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 5 (7 : Fin 8)).toFO
    textbookECodeAfterFiveFormula

def textbookECodeAfterTwoFormula : FOFormula 6 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 3 (6 : Fin 7)).toFO
    textbookECodeAfterThreeFormula

/--
The graph formula for the textbook constructor code.  Its free-variable layout
is `[omega, i, j, tag, m]`.

The seven existential witnesses, in order, are
`2`, `3`, `5`, `2 ^ i`, `3 ^ j`, `5 ^ tag`, and
`(2 ^ i) * (3 ^ j)`.  The final multiplication has output `m`.
-/
def textbookECodeFormula : FOFormula 5 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 2 (5 : Fin 6)).toFO
    textbookECodeAfterTwoFormula

/-! The following coordinate lemmas make every use of a quantified witness
explicit.  In particular, no arithmetic semantic lemma is applied to a tuple
until its four designated coordinates have been checked. -/

theorem textbookECode_powTwo_assignment {A : Type u}
    (s : Tuple A 5) (two three five powTwo : A) :
    let t := snoc (snoc (snoc (snoc s two) three) five) powTwo
    ![t (0 : Fin 9), t (5 : Fin 9), t (1 : Fin 9), t (8 : Fin 9)] =
      ![s 0, two, s 1, powTwo] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]

theorem textbookECode_powThree_assignment {A : Type u}
    (s : Tuple A 5) (two three five powTwo powThree : A) :
    let t := snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree
    ![t (0 : Fin 10), t (6 : Fin 10), t (2 : Fin 10),
      t (9 : Fin 10)] = ![s 0, three, s 2, powThree] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

theorem textbookECode_powFive_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive : A) :
    let t := snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive
    ![t (0 : Fin 11), t (7 : Fin 11), t (3 : Fin 11),
      t (10 : Fin 11)] = ![s 0, five, s 3, powFive] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

theorem textbookECode_product_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive product : A) :
    let t := snoc (snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive) product
    ![t (0 : Fin 12), t (8 : Fin 12), t (9 : Fin 12),
      t (11 : Fin 12)] = ![s 0, powTwo, powThree, product] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]

theorem textbookECode_final_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive product : A) :
    let t := snoc (snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive) product
    ![t (0 : Fin 12), t (11 : Fin 12), t (10 : Fin 12),
      t (4 : Fin 12)] = ![s 0, product, powFive, s 4] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

/-! ## Safe reuse in larger contexts -/

/-- Coordinate map for the free layout `[omega, i, j, tag, m]`. -/
def textbookECodeParametersAt {n : Nat}
    (omega i j tag m : Fin n) : Fin 5 -> Fin n :=
  ![omega, i, j, tag, m]

/-- The textbook code formula embedded into an arbitrary context. -/
def textbookECodeFormulaAt {n : Nat}
    (omega i j tag m : Fin n) : FOFormula n :=
  FOFormula.rename (textbookECodeParametersAt omega i j tag m)
    textbookECodeFormula

theorem comp_textbookECodeParametersAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega i j tag m : Fin n) :
    (fun k => s (textbookECodeParametersAt omega i j tag m k)) =
      ![s omega, s i, s j, s tag, s m] := by
  funext k
  fin_cases k <;> rfl

@[simp]
theorem satisfies_textbookECodeFormulaAt {A : Type u}
    (membership : A -> A -> Prop) {n : Nat}
    (omega i j tag m : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies membership
        (textbookECodeFormulaAt omega i j tag m) s <->
      FOFormula.Satisfies membership textbookECodeFormula
        ![s omega, s i, s j, s tag, s m] := by
  rw [textbookECodeFormulaAt, FOFormula.satisfies_rename,
    comp_textbookECodeParametersAt]

@[simp]
theorem satisfiesIn_textbookECodeFormulaAt
    (M : Set ZFSet.{u}) {n : Nat}
    (omega i j tag m : Fin n) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M
        (textbookECodeFormulaAt omega i j tag m) s <->
      Model.SatisfiesIn M textbookECodeFormula
        ![s omega, s i, s j, s tag, s m] := by
  rw [textbookECodeFormulaAt, satisfiesIn_rename_iff_eCode,
    comp_textbookECodeParametersAt]

/-! ## Exact ambient semantics -/

@[simp]
theorem satisfies_textbookECodeFormula_natCode_iff
    (i j tag : Nat) (m : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookECodeFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
          natCode j, natCode tag, m] <->
      m = natCode (textbookECode i j tag) := by
  rw [textbookECodeFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨two, htwoFormula, htail⟩
    have htwo : two = (natCode 2 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          2 (5 : Fin 6)
          (snoc ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
            natCode j, natCode tag, m] two)).mp htwoFormula
      change two = (natCode 2 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨three, hthreeFormula, htail⟩
    have hthree : three = (natCode 3 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          3 (6 : Fin 7)
          (snoc (snoc
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
              natCode j, natCode tag, m] two) three)).mp hthreeFormula
      change three = (natCode 3 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨five, hfiveFormula, htail⟩
    have hfive : five = (natCode 5 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          5 (7 : Fin 8)
          (snoc (snoc (snoc
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
              natCode j, natCode tag, m] two) three) five)).mp hfiveFormula
      change five = (natCode 5 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powTwo, hpowTwoFormula, htail⟩
    have hpowTwo :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), two, natCode i,
            powTwo] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powTwo_assignment] at hpowTwoFormula
      exact hpowTwoFormula
    rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powThree, hpowThreeFormula, htail⟩
    have hpowThree :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), three, natCode j,
            powThree] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powThree_assignment] at hpowThreeFormula
      exact hpowThreeFormula
    rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powFive, hpowFiveFormula, htail⟩
    have hpowFive :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), five, natCode tag,
            powFive] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powFive_assignment] at hpowFiveFormula
      exact hpowFiveFormula
    rw [textbookECodeAfterPowFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨product, hfinalConjunction⟩
    rw [textbookECodeFinalFormula, FOFormula.Satisfies] at hfinalConjunction
    rcases hfinalConjunction with ⟨hproductFormula, hfinalFormula⟩
    have hproduct :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), powTwo, powThree,
            product] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_product_assignment] at hproductFormula
      exact hproductFormula
    have hfinal :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), product, powFive, m] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_final_assignment] at hfinalFormula
      exact hfinalFormula
    subst two
    subst three
    subst five
    have hpowTwo' : powTwo = (natCode (2 ^ i) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 2 i powTwo).mp hpowTwo
    have hpowThree' : powThree = (natCode (3 ^ j) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 3 j powThree).mp hpowThree
    have hpowFive' : powFive = (natCode (5 ^ tag) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 5 tag powFive).mp hpowFive
    subst powTwo
    subst powThree
    subst powFive
    have hproduct' :
        product = (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) :=
      (satisfies_natMulFormula_natCode_iff
        (2 ^ i) (3 ^ j) product).mp hproduct
    subst product
    have hm :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfies_natMulFormula_natCode_iff
        ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mp hfinal
    simpa only [textbookECode, Nat.mul_assoc] using hm
  · intro hm
    have hm' :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hm
    refine ⟨natCode 2, ?_, ?_⟩
    · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        2 (5 : Fin 6) _).mpr
      change (natCode 2 : ZFSet.{u}) = natCode 2
      rfl
    · rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies]
      refine ⟨natCode 3, ?_, ?_⟩
      · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          3 (6 : Fin 7) _).mpr
        change (natCode 3 : ZFSet.{u}) = natCode 3
        rfl
      · rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies]
        refine ⟨natCode 5, ?_, ?_⟩
        · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
            5 (7 : Fin 8) _).mpr
          change (natCode 5 : ZFSet.{u}) = natCode 5
          rfl
        · rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies]
          refine ⟨natCode (2 ^ i), ?_, ?_⟩
          · rw [satisfies_natPowFormulaAt,
              textbookECode_powTwo_assignment]
            exact (satisfies_natPowFormula_natCode_iff
              2 i (natCode (2 ^ i))).mpr rfl
          · rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies]
            refine ⟨natCode (3 ^ j), ?_, ?_⟩
            · rw [satisfies_natPowFormulaAt,
                textbookECode_powThree_assignment]
              exact (satisfies_natPowFormula_natCode_iff
                3 j (natCode (3 ^ j))).mpr rfl
            · rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies]
              refine ⟨natCode (5 ^ tag), ?_, ?_⟩
              · rw [satisfies_natPowFormulaAt,
                  textbookECode_powFive_assignment]
                exact (satisfies_natPowFormula_natCode_iff
                  5 tag (natCode (5 ^ tag))).mpr rfl
              · rw [textbookECodeAfterPowFiveFormula,
                  FOFormula.Satisfies]
                refine ⟨natCode ((2 ^ i) * (3 ^ j)), ?_⟩
                rw [textbookECodeFinalFormula, FOFormula.Satisfies]
                constructor
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_product_assignment]
                  exact (satisfies_natMulFormula_natCode_iff
                    (2 ^ i) (3 ^ j)
                    (natCode ((2 ^ i) * (3 ^ j)))).mpr rfl
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_final_assignment]
                  exact (satisfies_natMulFormula_natCode_iff
                    ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mpr hm'

/-! ## Exact restricted semantics -/

theorem satisfiesIn_textbookECodeFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (i j tag : Nat) {m : ZFSet.{u}} (hmM : m ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookECodeFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
          natCode j, natCode tag, m] <->
      m = natCode (textbookECode i j tag) := by
  let s : Tuple ZFSet.{u} 5 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
      natCode j, natCode tag, m]
  have homegaM : (Ordinal.omega0.toZFSet : ZFSet.{u}) ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM j
  have htagM : (natCode tag : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM tag
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro k
    fin_cases k
    · exact homegaM
    · exact hiM
    · exact hjM
    · exact htagM
    · exact hmM
  change Model.SatisfiesIn (M : Set ZFSet.{u}) textbookECodeFormula s <-> _
  rw [textbookECodeFormula, Model.SatisfiesIn]
  constructor
  · rintro ⟨two, htwoM, htwoFormula, htail⟩
    have hsTwoM : Model.TupleIn (M : Set ZFSet.{u}) (snoc s two) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩
    have htwo : two = (natCode 2 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        2 (5 : Fin 6) (snoc s two) hsTwoM).mp htwoFormula
      change two = (natCode 2 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterTwoFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨three, hthreeM, hthreeFormula, htail⟩
    have hsThreeM :
        Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc s two) three) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsTwoM, hthreeM⟩
    have hthree : three = (natCode 3 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        3 (6 : Fin 7) (snoc (snoc s two) three) hsThreeM).mp
          hthreeFormula
      change three = (natCode 3 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterThreeFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨five, hfiveM, hfiveFormula, htail⟩
    have hsFiveM :
        Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc (snoc s two) three) five) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsThreeM, hfiveM⟩
    have hfive : five = (natCode 5 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        5 (7 : Fin 8) (snoc (snoc (snoc s two) three) five)
          hsFiveM).mp hfiveFormula
      change five = (natCode 5 : ZFSet.{u}) at h
      exact h
    subst two
    subst three
    subst five
    rw [textbookECodeAfterFiveFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powTwo, hpowTwoM, hpowTwoFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powTwo_assignment] at hpowTwoFormula
    have hpowTwo :
        powTwo = (natCode (2 ^ i) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 2 i hpowTwoM).mp hpowTwoFormula
    subst powTwo
    rw [textbookECodeAfterPowTwoFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powThree, hpowThreeM, hpowThreeFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powThree_assignment] at hpowThreeFormula
    have hpowThree :
        powThree = (natCode (3 ^ j) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 3 j hpowThreeM).mp hpowThreeFormula
    subst powThree
    rw [textbookECodeAfterPowThreeFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powFive, hpowFiveM, hpowFiveFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powFive_assignment] at hpowFiveFormula
    have hpowFive :
        powFive = (natCode (5 ^ tag) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 5 tag hpowFiveM).mp hpowFiveFormula
    subst powFive
    rw [textbookECodeAfterPowFiveFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨product, hproductM, hfinalConjunction⟩
    rw [textbookECodeFinalFormula, Model.SatisfiesIn] at hfinalConjunction
    rcases hfinalConjunction with ⟨hproductFormula, hfinalFormula⟩
    rw [satisfiesIn_natMulFormulaAt,
      textbookECode_product_assignment] at hproductFormula
    have hproduct :
        product = (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_natCode_iff
        hM (2 ^ i) (3 ^ j) hproductM).mp hproductFormula
    subst product
    rw [satisfiesIn_natMulFormulaAt,
      textbookECode_final_assignment] at hfinalFormula
    have hm :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_natCode_iff
        hM ((2 ^ i) * (3 ^ j)) (5 ^ tag) hmM).mp hfinalFormula
    simpa only [textbookECode, Nat.mul_assoc] using hm
  · intro hm
    have hm' :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hm
    have htwoM : (natCode 2 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 2
    have hthreeM : (natCode 3 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 3
    have hfiveM : (natCode 5 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 5
    have hpowTwoM : (natCode (2 ^ i) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (2 ^ i)
    have hpowThreeM : (natCode (3 ^ j) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (3 ^ j)
    have hpowFiveM : (natCode (5 ^ tag) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (5 ^ tag)
    have hproductM :
        (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM
        ((2 ^ i) * (3 ^ j))
    refine ⟨natCode 2, htwoM, ?_, ?_⟩
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        2 (5 : Fin 6) (snoc s (natCode 2))
        (Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩)).mpr
      change (natCode 2 : ZFSet.{u}) = natCode 2
      rfl
    · rw [textbookECodeAfterTwoFormula, Model.SatisfiesIn]
      refine ⟨natCode 3, hthreeM, ?_, ?_⟩
      · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
          3 (6 : Fin 7) _ ?_).mpr
        · change (natCode 3 : ZFSet.{u}) = natCode 3
          rfl
        · exact Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩, hthreeM⟩
      · rw [textbookECodeAfterThreeFormula, Model.SatisfiesIn]
        refine ⟨natCode 5, hfiveM, ?_, ?_⟩
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
            5 (7 : Fin 8) _ ?_).mpr
          · change (natCode 5 : ZFSet.{u}) = natCode 5
            rfl
          · exact Model.tupleIn_snoc_iff.mpr
              ⟨Model.tupleIn_snoc_iff.mpr
                ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩,
                  hthreeM⟩,
                hfiveM⟩
        · rw [textbookECodeAfterFiveFormula, Model.SatisfiesIn]
          refine ⟨natCode (2 ^ i), hpowTwoM, ?_, ?_⟩
          · rw [satisfiesIn_natPowFormulaAt,
              textbookECode_powTwo_assignment]
            exact (satisfiesIn_natPowFormula_natCode_iff
              hM 2 i hpowTwoM).mpr rfl
          · rw [textbookECodeAfterPowTwoFormula, Model.SatisfiesIn]
            refine ⟨natCode (3 ^ j), hpowThreeM, ?_, ?_⟩
            · rw [satisfiesIn_natPowFormulaAt,
                textbookECode_powThree_assignment]
              exact (satisfiesIn_natPowFormula_natCode_iff
                hM 3 j hpowThreeM).mpr rfl
            · rw [textbookECodeAfterPowThreeFormula, Model.SatisfiesIn]
              refine ⟨natCode (5 ^ tag), hpowFiveM, ?_, ?_⟩
              · rw [satisfiesIn_natPowFormulaAt,
                  textbookECode_powFive_assignment]
                exact (satisfiesIn_natPowFormula_natCode_iff
                  hM 5 tag hpowFiveM).mpr rfl
              · rw [textbookECodeAfterPowFiveFormula,
                  Model.SatisfiesIn]
                refine ⟨natCode ((2 ^ i) * (3 ^ j)), hproductM, ?_⟩
                rw [textbookECodeFinalFormula, Model.SatisfiesIn]
                constructor
                · rw [satisfiesIn_natMulFormulaAt,
                    textbookECode_product_assignment]
                  exact (satisfiesIn_natMulFormula_natCode_iff
                    hM (2 ^ i) (3 ^ j) hproductM).mpr rfl
                · rw [satisfiesIn_natMulFormulaAt,
                    textbookECode_final_assignment]
                  exact (satisfiesIn_natMulFormula_natCode_iff
                    hM ((2 ^ i) * (3 ^ j)) (5 ^ tag) hmM).mpr hm'

/-- Any restricted satisfying assignment has standard natural-number input
coordinates.  This is not an extra conjunct hidden in the coding formula: it
is forced by the three occurrences of the already verified exponentiation
graph. -/
theorem satisfiesIn_textbookECodeFormula_domain
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (s : Tuple ZFSet.{u} 5)
    (hsM : Model.TupleIn (M : Set ZFSet.{u}) s)
    (hformula : Model.SatisfiesIn (M : Set ZFSet.{u})
      textbookECodeFormula s) :
    s 0 = Ordinal.omega0.toZFSet /\
      exists i j tag : Nat,
        s 1 = natCode i /\ s 2 = natCode j /\ s 3 = natCode tag := by
  have hworking := hformula
  rw [textbookECodeFormula, Model.SatisfiesIn] at hworking
  rcases hworking with ⟨two, htwoM, _htwoFormula, htail⟩
  rw [textbookECodeAfterTwoFormula, Model.SatisfiesIn] at htail
  rcases htail with ⟨three, hthreeM, _hthreeFormula, htail⟩
  rw [textbookECodeAfterThreeFormula, Model.SatisfiesIn] at htail
  rcases htail with ⟨five, hfiveM, _hfiveFormula, htail⟩
  rw [textbookECodeAfterFiveFormula, Model.SatisfiesIn] at htail
  rcases htail with ⟨powTwo, hpowTwoM, hpowTwoFormula, htail⟩
  rw [satisfiesIn_natPowFormulaAt,
    textbookECode_powTwo_assignment] at hpowTwoFormula
  have hpowTwoInputsM : Model.TupleIn (M : Set ZFSet.{u})
      ![s 0, two, s 1] := by
    intro k
    fin_cases k
    · exact hsM 0
    · exact htwoM
    · exact hsM 1
  have hpowTwoGraph :=
    ((natPow_functionAbsoluteTo hM).2
      ![s 0, two, s 1] powTwo hpowTwoInputsM hpowTwoM).mp
      hpowTwoFormula
  rcases hpowTwoGraph.1 with
    ⟨homega, _base, i, _hbase, hi⟩
  rw [textbookECodeAfterPowTwoFormula, Model.SatisfiesIn] at htail
  rcases htail with ⟨powThree, hpowThreeM, hpowThreeFormula, htail⟩
  rw [satisfiesIn_natPowFormulaAt,
    textbookECode_powThree_assignment] at hpowThreeFormula
  have hpowThreeInputsM : Model.TupleIn (M : Set ZFSet.{u})
      ![s 0, three, s 2] := by
    intro k
    fin_cases k
    · exact hsM 0
    · exact hthreeM
    · exact hsM 2
  have hpowThreeGraph :=
    ((natPow_functionAbsoluteTo hM).2
      ![s 0, three, s 2] powThree
      hpowThreeInputsM hpowThreeM).mp hpowThreeFormula
  rcases hpowThreeGraph.1 with
    ⟨_homegaThree, _base, j, _hbase, hj⟩
  rw [textbookECodeAfterPowThreeFormula, Model.SatisfiesIn] at htail
  rcases htail with ⟨powFive, hpowFiveM, hpowFiveFormula, _htail⟩
  rw [satisfiesIn_natPowFormulaAt,
    textbookECode_powFive_assignment] at hpowFiveFormula
  have hpowFiveInputsM : Model.TupleIn (M : Set ZFSet.{u})
      ![s 0, five, s 3] := by
    intro k
    fin_cases k
    · exact hsM 0
    · exact hfiveM
    · exact hsM 3
  have hpowFiveGraph :=
    ((natPow_functionAbsoluteTo hM).2
      ![s 0, five, s 3] powFive hpowFiveInputsM hpowFiveM).mp
      hpowFiveFormula
  rcases hpowFiveGraph.1 with
    ⟨_homegaFive, _base, tag, _hbase, htag⟩
  exact ⟨homega, i, j, tag, hi, hj, htag⟩

/-! ## Total set-coded operation and function absoluteness -/

/-- Total ambient operation on arbitrary set codes.  Exactly as for the
arithmetic operations used to construct it, nonstandard inputs are sent to
the empty set; the represented domain below excludes those inputs. -/
noncomputable def textbookECodeZF
    (i j tag : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode i, textbookNatDecode j,
      textbookNatDecode tag with
  | some i, some j, some tag => natCode (textbookECode i j tag)
  | _, _, _ => ∅

@[simp]
theorem textbookECodeZF_natCode (i j tag : Nat) :
    textbookECodeZF (natCode i : ZFSet.{u}) (natCode j) (natCode tag) =
      natCode (textbookECode i j tag) := by
  simp [textbookECodeZF]

/-- Input domain for the parameter tuple `[omega, i, j, tag]`. -/
def TextbookECodeTupleDomain : Set (Tuple ZFSet.{u} 4) :=
  {s | s 0 = Ordinal.omega0.toZFSet /\
    exists i j tag : Nat,
      s 1 = natCode i /\ s 2 = natCode j /\ s 3 = natCode tag}

/-- Ambient value function represented by `textbookECodeFormula`. -/
noncomputable def textbookECodeTupleFunction
    (s : Tuple ZFSet.{u} 4) : ZFSet.{u} :=
  textbookECodeZF (s 1) (s 2) (s 3)

/-- The complete textbook code operation is absolute to every transitive set
model of ZF.  Its formula has output in the fifth coordinate and represents
exactly `2 ^ i * 3 ^ j * 5 ^ tag` on standard natural-number codes. -/
theorem textbookECode_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M) :
    Model.FunctionAbsoluteTo (M : Set ZFSet.{u})
      TextbookECodeTupleDomain textbookECodeTupleFunction
      textbookECodeFormula := by
  constructor
  · intro s _hsM hsDomain
    rcases hsDomain with
      ⟨_homega, i, j, tag, hi, hj, htag⟩
    rw [textbookECodeTupleFunction, hi, hj, htag,
      textbookECodeZF_natCode]
    exact Model.natCode_mem_of_isTransitiveZFModel hM
      (textbookECode i j tag)
  · intro s m hsM hmM
    constructor
    · intro hformula
      have hfullM : Model.TupleIn (M : Set ZFSet.{u}) (snoc s m) :=
        Model.tupleIn_snoc_iff.mpr ⟨hsM, hmM⟩
      have hdomain := satisfiesIn_textbookECodeFormula_domain
        hM (snoc s m) hfullM hformula
      rcases hdomain with
        ⟨homegaRaw, i, j, tag, hiRaw, hjRaw, htagRaw⟩
      have homega : s 0 = Ordinal.omega0.toZFSet := by
        rw [show (0 : Fin 5) = (0 : Fin 4).castSucc by rfl,
          snoc_castSucc] at homegaRaw
        exact homegaRaw
      have hi : s 1 = (natCode i : ZFSet.{u}) := by
        rw [show (1 : Fin 5) = (1 : Fin 4).castSucc by rfl,
          snoc_castSucc] at hiRaw
        exact hiRaw
      have hj : s 2 = (natCode j : ZFSet.{u}) := by
        rw [show (2 : Fin 5) = (2 : Fin 4).castSucc by rfl,
          snoc_castSucc] at hjRaw
        exact hjRaw
      have htag : s 3 = (natCode tag : ZFSet.{u}) := by
        rw [show (3 : Fin 5) = (3 : Fin 4).castSucc by rfl,
          snoc_castSucc] at htagRaw
        exact htagRaw
      have hassign : snoc s m =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
            natCode j, natCode tag, m] := by
        funext k
        fin_cases k
        · exact homega
        · exact hi
        · exact hj
        · exact htag
        · rfl
      rw [hassign] at hformula
      have hm : m = natCode (textbookECode i j tag) :=
        (satisfiesIn_textbookECodeFormula_natCode_iff
          hM i j tag hmM).mp hformula
      refine ⟨⟨homega, i, j, tag, hi, hj, htag⟩, ?_⟩
      rw [textbookECodeTupleFunction, hi, hj, htag,
        textbookECodeZF_natCode]
      exact hm
    · rintro ⟨⟨homega, i, j, tag, hi, hj, htag⟩, hm⟩
      have hfunction :
          textbookECodeTupleFunction s =
            natCode (textbookECode i j tag) := by
        rw [textbookECodeTupleFunction, hi, hj, htag,
          textbookECodeZF_natCode]
      have hmCode : m = natCode (textbookECode i j tag) :=
        hm.trans hfunction
      have hassign : snoc s m =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
            natCode j, natCode tag, m] := by
        funext k
        fin_cases k
        · exact homega
        · exact hi
        · exact hj
        · exact htag
        · rfl
      rw [hassign]
      exact (satisfiesIn_textbookECodeFormula_natCode_iff
        hM i j tag hmM).mpr hmCode

end TextbookNatFormula

end Constructible
