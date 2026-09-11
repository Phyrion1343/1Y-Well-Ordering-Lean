/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFSeparation

/-!
# Standard omega in transitive set models of ZF

This file proves that every transitive set model of ZF contains the ambient
von Neumann `omega`.  The proof does not assume that `omega` is already in the
model.

First, Infinity supplies an internal inductive set.  Separation inside the
model then constructs its least-inductive subset.  A second use of Separation
shows that every member of this subset is either empty or the successor of an
earlier member.  Ambient well-founded membership induction therefore rules
out nonstandard members, while ordinary natural-number induction gives the
opposite inclusion.

Both separated sets are obtained from the model's Separation scheme before
being identified with ambient `ZFSet.sep` descriptions.  No Power Set,
Replacement, Choice, or externally chosen family is used.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-! ## Elementary closure -/

/-- A transitive ZF model is closed under ambient von Neumann successor. -/
theorem successor_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    insert x x ∈ M := by
  have hsingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hpair : ({{x}, x} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hsingleton hx
  have hunion : ZFSet.sUnion ({{x}, x} : ZFSet.{u}) ∈ M :=
    sUnion_mem_of_isTransitiveZFModel hM hpair
  simpa only [ZFSet.sUnion_pair, ← ZFSet.insert_eq] using hunion

/-- Every standard finite ordinal belongs to a transitive ZF model. -/
theorem natOrdinal_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ M := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using
        empty_mem_of_isTransitiveZFModel hM
  | succ n ih =>
      have hsucc := successor_mem_of_isTransitiveZFModel hM ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hsucc

/-! ## Independent formulas for empty set, successor, and inductiveness -/

private theorem satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_disj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

private theorem satisfiesIn_imp_iff
    (M : Set ZFSet.{u}) {n : Nat} (antecedent consequent : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp antecedent consequent) s ↔
      (SatisfiesIn M antecedent s → SatisfiesIn M consequent s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_disj_iff, SatisfiesIn]
  tauto

/-- Coordinate `i` has no members. -/
def transitiveZFEmptyAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

/-- Coordinate `successor` is the von Neumann successor of `index`. -/
def transitiveZFSuccessorAt {n : Nat}
    (successor index : Fin n) : FOFormula n :=
  .conj
    (.mem index successor)
    (.conj
      (FOFormula.all
        (FOFormula.imp
          (.mem (Fin.last n) successor.castSucc)
          (FOFormula.disj
            (.mem (Fin.last n) index.castSucc)
            (.eq (Fin.last n) index.castSucc))))
      (FOFormula.all
        (FOFormula.imp
          (.mem (Fin.last n) index.castSucc)
          (.mem (Fin.last n) successor.castSucc))))

/-- Raw meaning of being inductive relative to the carrier `M`. -/
def ZFInductiveSetIn (M w : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ w ∧
    ∀ x : ZFSet.{u}, x ∈ M → x ∈ w → insert x x ∈ w

/-- Coordinate `i` is inductive, using the independent empty and successor
formulas above. -/
def transitiveZFInductiveAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (transitiveZFEmptyAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (transitiveZFSuccessorAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

/-- Restricted empty-set semantics over a transitive carrier. -/
theorem satisfiesIn_transitiveZFEmptyAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (transitiveZFEmptyAt i) s ↔
      s i = (∅ : ZFSet.{u}) := by
  rw [transitiveZFEmptyAt, satisfiesIn_all_iff]
  simp only [SatisfiesIn, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h z (htrans.mem_trans hz (hs i)) hz).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · intro h z _hzM hz
    rw [h] at hz
    exact (ZFSet.notMem_empty z hz).elim

/-- Restricted successor semantics over a transitive carrier. -/
theorem satisfiesIn_transitiveZFSuccessorAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive) {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (transitiveZFSuccessorAt successor index) s ↔
      s successor = insert (s index) (s index) := by
  rw [transitiveZFSuccessorAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff, satisfiesIn_imp_iff,
    satisfiesIn_disj_iff, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hforward, hbackward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      have hzM : z ∈ M := htrans.mem_trans hz (hs successor)
      rcases hforward z hzM hz with hzIndex | hzEq
      · exact Or.inr hzIndex
      · exact Or.inl hzEq
    · rintro (rfl | hz)
      · exact hindex
      · exact hbackward z (htrans.mem_trans hz (hs index)) hz
  · intro hsuccessor
    rw [hsuccessor]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro z _hzM hz
      rcases ZFSet.mem_insert_iff.mp hz with hzEq | hzIndex
      · exact Or.inr hzEq
      · exact Or.inl hzIndex
    · intro z _hzM hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr hz)

/-- The independent inductive-set formula has exactly its raw meaning over a
transitive carrier containing the empty set and closed under successor. -/
theorem satisfiesIn_transitiveZFInductiveAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hempty : (∅ : ZFSet.{u}) ∈ M)
    (hsuccessor : ∀ x : ZFSet.{u}, x ∈ M → insert x x ∈ M)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (transitiveZFInductiveAt i) s ↔
      ZFInductiveSetIn M (s i) := by
  simp only [transitiveZFInductiveAt, SatisfiesIn, satisfiesIn_all_iff,
    satisfiesIn_imp_iff, snoc_last, snoc_castSucc, ZFInductiveSetIn]
  constructor
  · rintro ⟨⟨e, heM, heEmpty, heMem⟩, hsucc⟩
    have he : e = (∅ : ZFSet.{u}) := by
      simpa only [snoc_last] using
        (satisfiesIn_transitiveZFEmptyAt_iff htrans
          (Fin.last n) (snoc s e) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using heM
            · simpa using hs k)).mp heEmpty
    constructor
    · simpa only [he] using heMem
    · intro x hxM hxw
      rcases hsucc x hxM hxw with
        ⟨next, hnextM, hnextFormula, hnextMem⟩
      have hnext : next = insert x x := by
        simpa only [snoc_last, snoc_castSucc] using
          (satisfiesIn_transitiveZFSuccessorAt_iff htrans
            (Fin.last (n + 1)) (Fin.last n).castSucc
            (snoc (snoc s x) next) (by
              intro j
              refine Fin.lastCases ?_ (fun j' => ?_) j
              · simpa using hnextM
              · refine Fin.lastCases ?_ (fun k => ?_) j'
                · simpa using hxM
                · simpa using hs k)).mp hnextFormula
      simpa only [hnext] using hnextMem
  · rintro ⟨hemptyMem, hsucc⟩
    constructor
    · refine ⟨∅, hempty, ?_, hemptyMem⟩
      apply (satisfiesIn_transitiveZFEmptyAt_iff htrans
        (Fin.last n) (snoc s (∅ : ZFSet.{u})) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hempty
          · simpa using hs k)).mpr
      simp only [snoc_last]
    · intro x hxM hxw
      refine ⟨insert x x, hsuccessor x hxM, ?_, hsucc x hxM hxw⟩
      apply (satisfiesIn_transitiveZFSuccessorAt_iff htrans
        (Fin.last (n + 1)) (Fin.last n).castSucc
        (snoc (snoc s x) (insert x x)) (by
          intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · simpa using hsuccessor x hxM
          · refine Fin.lastCases ?_ (fun k => ?_) j'
            · simpa using hxM
            · simpa using hs k)).mpr
      simp only [snoc_last, snoc_castSucc]

/-! ## The internal least inductive set -/

/-- The unary predicate saying that its argument belongs to every inductive
set in the model. -/
def memberOfEveryInductiveFormula : FOFormula 1 :=
  FOFormula.all
    (FOFormula.imp
      (transitiveZFInductiveAt (Fin.last 1))
      (.mem (0 : Fin 2) (Fin.last 1)))

/-- Exact restricted semantics of `memberOfEveryInductiveFormula`. -/
theorem satisfiesIn_memberOfEveryInductiveFormula_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (s : Tuple ZFSet.{u} 1) (hs : s 0 ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) memberOfEveryInductiveFormula s ↔
      ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w → s 0 ∈ w := by
  have hempty : (∅ : ZFSet.{u}) ∈ M :=
    empty_mem_of_isTransitiveZFModel hM
  have hsuccessor : ∀ x : ZFSet.{u}, x ∈ M → insert x x ∈ M :=
    fun x hx => successor_mem_of_isTransitiveZFModel hM hx
  rw [memberOfEveryInductiveFormula, satisfiesIn_all_iff]
  constructor
  · intro h w hwM hwInd
    have himp :=
      (satisfiesIn_imp_iff (M : Set ZFSet.{u})
        (transitiveZFInductiveAt (Fin.last 1))
        (.mem (0 : Fin 2) (Fin.last 1)) (snoc s w)).mp
        (h w hwM)
    apply himp
    apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1 hempty
      hsuccessor (Fin.last 1) (snoc s w) (by
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · change w ∈ M
          exact hwM
        · rw [snoc_castSucc]
          have hk : k = 0 := Fin.eq_zero k
          simpa only [hk] using hs)).mpr
    exact hwInd
  · intro h w hwM
    apply (satisfiesIn_imp_iff (M : Set ZFSet.{u})
      (transitiveZFInductiveAt (Fin.last 1))
      (.mem (0 : Fin 2) (Fin.last 1)) (snoc s w)).mpr
    intro hwFormula
    have hwInd : ZFInductiveSetIn M w :=
      (satisfiesIn_transitiveZFInductiveAt_iff hM.1 hempty
        hsuccessor (Fin.last 1) (snoc s w) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change w ∈ M
            exact hwM
          · rw [snoc_castSucc]
            have hk : k = 0 := Fin.eq_zero k
            simpa only [hk] using hs)).mp hwFormula
    change s 0 ∈ w
    exact h w hwM hwInd

/-- Infinity supplies an ambiently recognized inductive member of a
transitive ZF model. -/
theorem exists_zfCarrier_inductiveSetIn
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    ∃ w : ZFCarrier M, ZFInductiveSetIn M w.1 := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .infinity with
    ⟨w, ⟨e, hew, heEmpty⟩, hsucc⟩
  refine ⟨w, ?_⟩
  have he : e.1 = (∅ : ZFSet.{u}) := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hze
      have hzM : z ∈ M := hM.1.mem_trans hze e.2
      exact (heEmpty ⟨z, hzM⟩ hze).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  constructor
  · rw [← he]
    exact hew
  · intro x hxM hxw
    let xM : ZFCarrier M := ⟨x, hxM⟩
    rcases hsucc xM hxw with ⟨y, hyw, hy⟩
    have hyEq : y.1 = insert x x := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_insert_iff]
      constructor
      · intro hzy
        have hzM : z ∈ M := hM.1.mem_trans hzy y.2
        rcases (hy ⟨z, hzM⟩).mp hzy with hzx | hzx
        · exact Or.inr hzx
        · exact Or.inl (congrArg Subtype.val hzx)
      · rintro (rfl | hzx)
        · exact (hy xM).mpr (Or.inr rfl)
        · have hzM : z ∈ M := hM.1.mem_trans hzx hxM
          exact (hy ⟨z, hzM⟩).mpr (Or.inl hzx)
    rw [← hyEq]
    exact hyw

/-- The model contains an internally least inductive set.  Both existence and
minimality are obtained from Infinity and the model's Separation scheme. -/
theorem exists_zfCarrier_leastInductiveSet
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    ∃ omegaM : ZFCarrier M,
      ZFInductiveSetIn M omegaM.1 ∧
        ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w → omegaM.1 ⊆ w := by
  rcases exists_zfCarrier_inductiveSetIn hM with ⟨w, hwInd⟩
  let noParams : Tuple (ZFCarrier M) 0 := fun i => Fin.elim0 i
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM
      memberOfEveryInductiveFormula noParams w with ⟨omegaM, homegaM⟩
  have hspec (x : ZFSet.{u}) :
      x ∈ omegaM.1 ↔
        x ∈ w.1 ∧
          ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v := by
    rw [homegaM, ZFSet.mem_sep]
    constructor
    · rintro ⟨hxw, hxFormula⟩
      have hxM : x ∈ M := hM.1.mem_trans hxw w.2
      refine ⟨hxw, ?_⟩
      have hsemantic :=
        (satisfiesIn_memberOfEveryInductiveFormula_iff hM
          (snoc (zfCarrierTupleVal noParams) x) (by
            change x ∈ M
            exact hxM)).mp hxFormula
      change ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v at hsemantic
      exact hsemantic
    · rintro ⟨hxw, hxAll⟩
      have hxM : x ∈ M := hM.1.mem_trans hxw w.2
      refine ⟨hxw, ?_⟩
      apply (satisfiesIn_memberOfEveryInductiveFormula_iff hM
        (snoc (zfCarrierTupleVal noParams) x) (by
          change x ∈ M
          exact hxM)).mpr
      change ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v
      exact hxAll
  have homegaInd : ZFInductiveSetIn M omegaM.1 := by
    constructor
    · apply (hspec (∅ : ZFSet.{u})).mpr
      refine ⟨hwInd.1, ?_⟩
      intro v _hvM hvInd
      exact hvInd.1
    · intro x hxM hxOmega
      have hxSpec := (hspec x).mp hxOmega
      apply (hspec (insert x x)).mpr
      refine ⟨hwInd.2 x hxM hxSpec.1, ?_⟩
      intro v hvM hvInd
      exact hvInd.2 x hxM (hxSpec.2 v hvM hvInd)
  refine ⟨omegaM, homegaInd, ?_⟩
  intro v hvM hvInd x hxOmega
  exact ((hspec x).mp hxOmega).2 v hvM hvInd

/-! ## Successor decomposition of the internal omega -/

/-- With assignment `(omegaM, x)`, assert that `x` is empty or is the
successor of some member of `omegaM`. -/
def zeroOrSuccessorInFormula : FOFormula 2 :=
  FOFormula.disj
    (transitiveZFEmptyAt (1 : Fin 2))
    (.ex (.conj
      (.mem (2 : Fin 3) (0 : Fin 3))
      (transitiveZFSuccessorAt (1 : Fin 3) (2 : Fin 3))))

/-- Exact restricted semantics of the zero-or-successor formula. -/
theorem satisfiesIn_zeroOrSuccessorInFormula_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (s : Tuple ZFSet.{u} 2) (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) zeroOrSuccessorInFormula s ↔
      s 1 = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ s 0 ∧
          s 1 = insert y y := by
  rw [zeroOrSuccessorInFormula, satisfiesIn_disj_iff]
  constructor
  · rintro (hzero | hsucc)
    · exact Or.inl
        ((satisfiesIn_transitiveZFEmptyAt_iff hM.1
          (1 : Fin 2) s hs).mp hzero)
    · rcases hsucc with ⟨y, hyM, hyOmega, hySucc⟩
      refine Or.inr ⟨y, hyM, hyOmega, ?_⟩
      exact (satisfiesIn_transitiveZFSuccessorAt_iff hM.1
        (1 : Fin 3) (2 : Fin 3) (snoc s y) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y ∈ M
            exact hyM
          · rw [snoc_castSucc]
            exact hs k)).mp hySucc
  · rintro (hzero | ⟨y, hyM, hyOmega, hySucc⟩)
    · exact Or.inl
        ((satisfiesIn_transitiveZFEmptyAt_iff hM.1
          (1 : Fin 2) s hs).mpr hzero)
    · refine Or.inr ⟨y, hyM, hyOmega, ?_⟩
      apply (satisfiesIn_transitiveZFSuccessorAt_iff hM.1
        (1 : Fin 3) (2 : Fin 3) (snoc s y) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y ∈ M
            exact hyM
          · rw [snoc_castSucc]
            exact hs k)).mpr
      exact hySucc

/-- Every member of an internally least inductive set is empty or an ambient
von Neumann successor of another member.  The auxiliary inductive subset is
obtained by a second application of the model's Separation scheme. -/
theorem mem_leastInductiveSet_zero_or_successor
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (omegaM : ZFCarrier M)
    (homegaInd : ZFInductiveSetIn M omegaM.1)
    (hminimal : ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w →
      omegaM.1 ⊆ w)
    {x : ZFSet.{u}} (hxOmega : x ∈ omegaM.1) :
    x = (∅ : ZFSet.{u}) ∨
      ∃ y : ZFSet.{u}, y ∈ omegaM.1 ∧ x = insert y y := by
  let omegaParam : Tuple (ZFCarrier M) 1 := fun _ => omegaM
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM
      zeroOrSuccessorInFormula omegaParam omegaM with ⟨closed, hclosed⟩
  have hspec (z : ZFSet.{u}) :
      z ∈ closed.1 ↔
        z ∈ omegaM.1 ∧
          (z = (∅ : ZFSet.{u}) ∨
            ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧
              z = insert y y) := by
    rw [hclosed, ZFSet.mem_sep]
    constructor
    · rintro ⟨hzOmega, hzFormula⟩
      have hzM : z ∈ M := hM.1.mem_trans hzOmega omegaM.2
      refine ⟨hzOmega, ?_⟩
      have hsemantic :=
        (satisfiesIn_zeroOrSuccessorInFormula_iff hM
          (snoc (zfCarrierTupleVal omegaParam) z) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · change z ∈ M
              exact hzM
            · rw [snoc_castSucc]
              exact (omegaParam k).2)).mp hzFormula
      change z = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧ z = insert y y at hsemantic
      exact hsemantic
    · rintro ⟨hzOmega, hzShape⟩
      have hzM : z ∈ M := hM.1.mem_trans hzOmega omegaM.2
      refine ⟨hzOmega, ?_⟩
      apply (satisfiesIn_zeroOrSuccessorInFormula_iff hM
        (snoc (zfCarrierTupleVal omegaParam) z) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change z ∈ M
            exact hzM
          · rw [snoc_castSucc]
            exact (omegaParam k).2)).mpr
      change z = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧ z = insert y y
      exact hzShape
  have hclosedInd : ZFInductiveSetIn M closed.1 := by
    constructor
    · apply (hspec (∅ : ZFSet.{u})).mpr
      exact ⟨homegaInd.1, Or.inl rfl⟩
    · intro z hzM hzClosed
      have hzOmega : z ∈ omegaM.1 := (hspec z).mp hzClosed |>.1
      have hsuccOmega : insert z z ∈ omegaM.1 :=
        homegaInd.2 z hzM hzOmega
      apply (hspec (insert z z)).mpr
      exact ⟨hsuccOmega, Or.inr ⟨z, hzM, hzOmega, rfl⟩⟩
  have hxClosed : x ∈ closed.1 :=
    hminimal closed.1 closed.2 hclosedInd hxOmega
  rcases ((hspec x).mp hxClosed).2 with hzero | ⟨y, _hyM, hyOmega, hsucc⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨y, hyOmega, hsucc⟩

/-! ## Identification with the standard omega -/

/-- The ambient standard omega is inductive relative to every carrier. -/
theorem omegaToZFSet_isInductiveSetIn (M : ZFSet.{u}) :
    ZFInductiveSetIn M Ordinal.omega0.toZFSet := by
  constructor
  · rw [Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro x _hxM hxOmega
    rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
    rw [← Ordinal.toZFSet_add_one]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (by
        rw [← Order.succ_eq_add_one]
        exact Ordinal.isSuccLimit_omega0.succ_lt halpha)

/-- Every standard finite ordinal belongs to an inductive set whose ambient
carrier contains all standard finite ordinals. -/
theorem natOrdinal_mem_of_ZFInductiveSetIn
    {M w : ZFSet.{u}} (hw : ZFInductiveSetIn M w)
    (hnM : ∀ n : Nat, (n : Ordinal.{u}).toZFSet ∈ M)
    (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ w := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (n : Ordinal.{u}).toZFSet (hnM n) ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hnext

/-- An internally least inductive set in a transitive ZF model is exactly the
ambient standard von Neumann omega. -/
theorem zfCarrier_leastInductiveSet_eq_omega
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (omegaM : ZFCarrier M)
    (homegaInd : ZFInductiveSetIn M omegaM.1)
    (hminimal : ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w →
      omegaM.1 ⊆ w) :
    omegaM.1 = Ordinal.omega0.toZFSet := by
  have hnM : ∀ n : Nat, (n : Ordinal.{u}).toZFSet ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM
  have homegaSubset : Ordinal.omega0.toZFSet ⊆ omegaM.1 := by
    intro x hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    rcases Ordinal.lt_omega0.mp halpha with ⟨n, rfl⟩
    exact natOrdinal_mem_of_ZFInductiveSetIn homegaInd hnM n
  have hsubsetOmega : omegaM.1 ⊆ Ordinal.omega0.toZFSet := by
    intro x hxOmega
    refine ZFSet.inductionOn
      (p := fun x : ZFSet.{u} =>
        x ∈ omegaM.1 → x ∈ Ordinal.omega0.toZFSet) x ?_ hxOmega
    intro x ih hxInternal
    rcases mem_leastInductiveSet_zero_or_successor hM omegaM
        homegaInd hminimal hxInternal with hzero | ⟨y, hyInternal, hsucc⟩
    · rw [hzero]
      exact (omegaToZFSet_isInductiveSetIn M).1
    · have hyx : y ∈ x := by
        rw [hsucc]
        exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
      have hyOmega : y ∈ Ordinal.omega0.toZFSet :=
        ih y hyx hyInternal
      have hyM : y ∈ M := hM.1.mem_trans hyInternal omegaM.2
      rw [hsucc]
      exact (omegaToZFSet_isInductiveSetIn M).2 y hyM hyOmega
  exact ZFSet.ext fun x => ⟨fun hx => hsubsetOmega hx,
    fun hx => homegaSubset hx⟩

/-- Every transitive set model of ZF contains the ambient standard omega. -/
theorem omega_toZFSet_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    Ordinal.omega0.toZFSet ∈ M := by
  rcases exists_zfCarrier_leastInductiveSet hM with
    ⟨omegaM, homegaInd, hminimal⟩
  have heq : omegaM.1 = Ordinal.omega0.toZFSet :=
    zfCarrier_leastInductiveSet_eq_omega hM omegaM homegaInd hminimal
  rw [← heq]
  exact omegaM.2

end

end Constructible.Model
