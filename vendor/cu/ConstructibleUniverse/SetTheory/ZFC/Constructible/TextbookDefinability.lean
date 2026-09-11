/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity

/-!
# The textbook sets of definable relations

This file internalizes the standard-natural-number core of the definitions in
Wang Fangting, *Axiomatic Set Theory*, Section 6.4.  In contrast with the
external relation algebra in `Def.lean`, every object defined here is a
genuine `ZFSet`.  The finite arities and indices in this file are Lean
`Nat`s; the total interface on set-coded indices is supplied separately in
`TextbookDefinabilityCode`.

For a natural number `n`, `textbookTupleSpace a n` is the set-theoretic
function space `a^n`: its members are Kuratowski graphs of functions from the
von Neumann ordinal `n` to `a`.  The definitions of `textbookDInZF`,
`textbookDEqZF`, `textbookExistsProjZF`, `textbookDStageZF`, and
`textbookDfZF` follow the display on textbook page 127.  In particular, the
exceptional convention

`P_exists(a, 0, r) = empty`

is part of the definition, rather than an after-the-fact simplification.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Finite tuple graphs -/

/-- The textbook finite power `a^n`, represented by actual function graphs. -/
noncomputable def textbookTupleSpace (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.funs (natCode n) a

@[simp]
theorem mem_textbookTupleSpace_iff {a s : ZFSet.{u}} {n : Nat} :
    s ∈ textbookTupleSpace a n ↔ ZFSet.IsFunc (natCode n) a s := by
  simp [textbookTupleSpace]

/-- The Kuratowski graph of an externally supplied `n`-tuple from `a`. -/
noncomputable def textbookTupleGraph {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) : ZFSet.{u} :=
  ZFSet.range fun i : Fin n => ZFSet.pair (natCode i.1) (s i).1

@[simp]
theorem mem_textbookTupleGraph_iff {a q : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    q ∈ textbookTupleGraph s ↔
      ∃ i : Fin n, ZFSet.pair (natCode i.1) (s i).1 = q := by
  simp [textbookTupleGraph]

@[simp]
theorem textbookTupleGraph_value {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    ZFSet.pair (natCode i.1) (s i).1 ∈ textbookTupleGraph s := by
  change ZFSet.pair (natCode i.1) (s i).1 ∈
    ZFSet.range (fun j : Fin n => ZFSet.pair (natCode j.1) (s j).1)
  exact ZFSet.mem_range_self
    (f := fun j : Fin n =>
      (ZFSet.pair (natCode j.1) (s j).1 : ZFSet.{u})) i

theorem mem_natCode_iff_exists_fin (z : ZFSet.{u}) (n : Nat) :
    z ∈ (natCode n : ZFSet.{u}) ↔
      ∃ i : Fin n, z = natCode i.1 := by
  rw [IndexedSequenceZF.mem_natCode_iff_exists_lt]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩

theorem textbookTupleGraph_isFunc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    ZFSet.IsFunc (natCode n) a (textbookTupleGraph s) := by
  constructor
  · intro q hq
    rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, rfl⟩
    rw [ZFSet.pair_mem_prod]
    exact ⟨(mem_natCode_iff_exists_fin _ _).mpr ⟨i, rfl⟩, (s i).2⟩
  · intro z hz
    rcases (mem_natCode_iff_exists_fin z n).mp hz with ⟨i, rfl⟩
    refine ⟨(s i).1, textbookTupleGraph_value s i, ?_⟩
    intro y hy
    rcases (mem_textbookTupleGraph_iff s).mp hy with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hij : i.1 = j.1 := (natCode_injective hparts.1).symm
    have hfin : i = j := Fin.ext hij
    subst j
    exact hparts.2.symm

@[simp]
theorem textbookTupleGraph_mem_tupleSpace {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookTupleSpace a n := by
  exact mem_textbookTupleSpace_iff.mpr (textbookTupleGraph_isFunc s)

theorem textbookTupleGraph_value_iff {a x : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    ZFSet.pair (natCode i.1) x ∈ textbookTupleGraph s ↔ x = (s i).1 := by
  constructor
  · intro hx
    rcases (mem_textbookTupleGraph_iff s).mp hx with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hij : i.1 = j.1 := natCode_injective hparts.1.symm
    have hfin : i = j := Fin.ext hij
    subst j
    exact hparts.2.symm
  · rintro rfl
    exact textbookTupleGraph_value s i

/-! ## Atomic relations and projection -/

/-- The standard-`Nat` core of the textbook relation `D_in(a,n,i,j)`, with
illegal indices giving `empty`. -/
noncomputable def textbookDInZF
    (a : ZFSet.{u}) (n i j : Nat) : ZFSet.{u} :=
  ZFSet.sep
    (fun s =>
      i < n ∧ j < n ∧
        ∃ x y : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) y ∈ s ∧ x ∈ y)
    (textbookTupleSpace a n)

@[simp]
theorem mem_textbookDInZF_iff {a s : ZFSet.{u}} {n i j : Nat} :
    s ∈ textbookDInZF a n i j ↔
      s ∈ textbookTupleSpace a n ∧ i < n ∧ j < n ∧
        ∃ x y : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) y ∈ s ∧ x ∈ y := by
  simp [textbookDInZF]

/-- The standard-`Nat` core of the textbook relation `D_eq(a,n,i,j)`, with
illegal indices giving `empty`. -/
noncomputable def textbookDEqZF
    (a : ZFSet.{u}) (n i j : Nat) : ZFSet.{u} :=
  ZFSet.sep
    (fun s =>
      i < n ∧ j < n ∧
        ∃ x : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) x ∈ s)
    (textbookTupleSpace a n)

@[simp]
theorem mem_textbookDEqZF_iff {a s : ZFSet.{u}} {n i j : Nat} :
    s ∈ textbookDEqZF a n i j ↔
      s ∈ textbookTupleSpace a n ∧ i < n ∧ j < n ∧
        ∃ x : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) x ∈ s := by
  simp [textbookDEqZF]

@[simp]
theorem textbookDInZF_eq_empty_of_not_lt_left {a : ZFSet.{u}}
    {n i j : Nat} (hi : ¬i < n) : textbookDInZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hi (mem_textbookDInZF_iff.mp hs).2.1

@[simp]
theorem textbookDInZF_eq_empty_of_not_lt_right {a : ZFSet.{u}}
    {n i j : Nat} (hj : ¬j < n) : textbookDInZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hj (mem_textbookDInZF_iff.mp hs).2.2.1

@[simp]
theorem textbookDEqZF_eq_empty_of_not_lt_left {a : ZFSet.{u}}
    {n i j : Nat} (hi : ¬i < n) : textbookDEqZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hi (mem_textbookDEqZF_iff.mp hs).2.1

@[simp]
theorem textbookDEqZF_eq_empty_of_not_lt_right {a : ZFSet.{u}}
    {n i j : Nat} (hj : ¬j < n) : textbookDEqZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hj (mem_textbookDEqZF_iff.mp hs).2.2.1

theorem textbookDInZF_subset_tupleSpace
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDInZF a n i j ⊆ textbookTupleSpace a n :=
  ZFSet.sep_subset

theorem textbookDEqZF_subset_tupleSpace
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDEqZF a n i j ⊆ textbookTupleSpace a n :=
  ZFSet.sep_subset

@[simp]
theorem textbookTupleGraph_mem_DInZF_iff {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i j : Fin n) :
    textbookTupleGraph s ∈ textbookDInZF a n i.1 j.1 ↔
      (s i).1 ∈ (s j).1 := by
  rw [mem_textbookDInZF_iff]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and, i.2, j.2]
  constructor
  · rintro ⟨x, y, hix, hjy, hxy⟩
    rw [textbookTupleGraph_value_iff s i] at hix
    rw [textbookTupleGraph_value_iff s j] at hjy
    simpa [hix, hjy] using hxy
  · intro hxy
    exact ⟨(s i).1, (s j).1,
      textbookTupleGraph_value s i, textbookTupleGraph_value s j, hxy⟩

@[simp]
theorem textbookTupleGraph_mem_DEqZF_iff {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i j : Fin n) :
    textbookTupleGraph s ∈ textbookDEqZF a n i.1 j.1 ↔ s i = s j := by
  rw [mem_textbookDEqZF_iff]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and, i.2, j.2]
  constructor
  · rintro ⟨x, hix, hjx⟩
    rw [textbookTupleGraph_value_iff s i] at hix
    rw [textbookTupleGraph_value_iff s j] at hjx
    apply Subtype.ext
    exact hix.symm.trans hjx
  · intro hij
    have hval : (s i).1 = (s j).1 := congrArg Subtype.val hij
    refine ⟨(s i).1, textbookTupleGraph_value s i, ?_⟩
    rw [hval]
    exact textbookTupleGraph_value s j

/-- Adjoin the last coordinate to a finite function graph. -/
noncomputable def textbookTupleSnocGraph
    (s : ZFSet.{u}) (n : Nat) (x : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair (natCode n) x) s

theorem textbookTupleGraph_snoc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (x : ZFCarrier a) :
    textbookTupleGraph (snoc s x) =
      textbookTupleSnocGraph (textbookTupleGraph s) n x.1 := by
  apply ZFSet.ext
  intro q
  rw [mem_textbookTupleGraph_iff]
  simp only [textbookTupleSnocGraph, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j hi => ?_) i
    · intro hi
      left
      simpa using hi.symm
    · right
      apply (mem_textbookTupleGraph_iff s).mpr
      exact ⟨j, by simpa using hi⟩
  · rintro (hq | hq)
    · exact ⟨Fin.last n, by simpa using hq.symm⟩
    · rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, hi⟩
      exact ⟨i.castSucc, by simpa using hi⟩

/--
The textbook existential projection.  The `n = 0` branch is deliberately
empty, exactly as stipulated on page 127.
-/
noncomputable def textbookExistsProjZF
    (a : ZFSet.{u}) (n : Nat) (r : ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then ∅
  else
    ZFSet.sep
      (fun s =>
        ∃ x ∈ a, textbookTupleSnocGraph s n x ∈ r)
      (textbookTupleSpace a n)

@[simp]
theorem textbookExistsProjZF_zero (a r : ZFSet.{u}) :
    textbookExistsProjZF a 0 r = ∅ := by
  simp [textbookExistsProjZF]

theorem mem_textbookExistsProjZF_iff {a r s : ZFSet.{u}}
    {n : Nat} (hn : n ≠ 0) :
    s ∈ textbookExistsProjZF a n r ↔
      s ∈ textbookTupleSpace a n ∧
        ∃ x ∈ a, textbookTupleSnocGraph s n x ∈ r := by
  simp [textbookExistsProjZF, hn]

theorem textbookExistsProjZF_subset_tupleSpace
    (a : ZFSet.{u}) (n : Nat) (r : ZFSet.{u}) :
    textbookExistsProjZF a n r ⊆ textbookTupleSpace a n := by
  by_cases hn : n = 0
  · subst n
    simp
  · intro s hs
    exact (mem_textbookExistsProjZF_iff hn).mp hs |>.1

theorem textbookTupleGraph_mem_existsProjZF_iff
    {a r : ZFSet.{u}} {n : Nat} (hn : n ≠ 0)
    (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookExistsProjZF a n r ↔
      ∃ x : ZFCarrier a, textbookTupleGraph (snoc s x) ∈ r := by
  rw [mem_textbookExistsProjZF_iff hn]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and]
  constructor
  · rintro ⟨x, hx, hsx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rwa [textbookTupleGraph_snoc]
  · rintro ⟨x, hsx⟩
    refine ⟨x.1, x.2, ?_⟩
    rwa [← textbookTupleGraph_snoc]

/-! ## The finite stages `D(k,a,n)` -/

/-- The two finite families of atomic `n`-ary relations. -/
noncomputable def textbookDZeroZF (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.range
      (fun p : Fin n × Fin n => textbookDInZF a n p.1.1 p.2.1) ∪
    ZFSet.range
      (fun p : Fin n × Fin n => textbookDEqZF a n p.1.1 p.2.1)

@[simp]
theorem mem_textbookDZeroZF_iff {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDZeroZF a n ↔
      (∃ i j : Fin n, textbookDInZF a n i.1 j.1 = r) ∨
        ∃ i j : Fin n, textbookDEqZF a n i.1 j.1 = r := by
  simp only [textbookDZeroZF, ZFSet.mem_union, ZFSet.mem_range]
  constructor
  · rintro (⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩)
    · exact Or.inl ⟨i, j, h⟩
    · exact Or.inr ⟨i, j, h⟩
  · rintro (⟨i, j, h⟩ | ⟨i, j, h⟩)
    · exact Or.inl ⟨(i, j), h⟩
    · exact Or.inr ⟨(i, j), h⟩

@[simp]
theorem textbookDZeroZF_zero (a : ZFSet.{u}) :
    textbookDZeroZF a 0 = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro r hr
  rcases mem_textbookDZeroZF_iff.mp hr with
    ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact Fin.elim0 i

/-- Complements, always taken relative to the finite power `a^n`. -/
noncomputable def textbookComplementFamilyZF
    (a : ZFSet.{u}) (n : Nat) (stage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun r : ZFCarrier stage => textbookTupleSpace a n \ r.1

@[simp]
theorem mem_textbookComplementFamilyZF_iff
    {a stage z : ZFSet.{u}} {n : Nat} :
    z ∈ textbookComplementFamilyZF a n stage ↔
      ∃ r ∈ stage, textbookTupleSpace a n \ r = z := by
  simp [textbookComplementFamilyZF]

/-- Pairwise intersections of members of one finite stage. -/
noncomputable def textbookIntersectionFamilyZF
    (stage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun p : ZFCarrier stage × ZFCarrier stage => p.1.1 ∩ p.2.1

@[simp]
theorem mem_textbookIntersectionFamilyZF_iff
    {stage z : ZFSet.{u}} :
    z ∈ textbookIntersectionFamilyZF stage ↔
      ∃ r ∈ stage, ∃ t ∈ stage, r ∩ t = z := by
  simp only [textbookIntersectionFamilyZF, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨r, t⟩, h⟩
    exact ⟨r.1, r.2, t.1, t.2, h⟩
  · rintro ⟨r, hr, t, ht, h⟩
    exact ⟨(⟨r, hr⟩, ⟨t, ht⟩), h⟩

/-- Existential projections of every `(n+1)`-ary relation in a stage. -/
noncomputable def textbookProjectionFamilyZF
    (a : ZFSet.{u}) (n : Nat) (higherStage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun r : ZFCarrier higherStage =>
    textbookExistsProjZF a n r.1

@[simp]
theorem mem_textbookProjectionFamilyZF_iff
    {a higherStage z : ZFSet.{u}} {n : Nat} :
    z ∈ textbookProjectionFamilyZF a n higherStage ↔
      ∃ r ∈ higherStage, textbookExistsProjZF a n r = z := by
  simp [textbookProjectionFamilyZF]

/--
The standard-`Nat` core of the textbook finite closure stages.  Recursion is
on `k` simultaneously for all arities, so the projection branch may use stage
`k` at arity `n+1`.
-/
noncomputable def textbookDStageZF (a : ZFSet.{u}) : Nat → Nat → ZFSet.{u}
  | 0, n => textbookDZeroZF a n
  | k + 1, n =>
      let current := textbookDStageZF a k n
      current ∪ textbookComplementFamilyZF a n current ∪
        textbookIntersectionFamilyZF current ∪
          textbookProjectionFamilyZF a n (textbookDStageZF a k (n + 1))

@[simp]
theorem textbookDStageZF_zero (a : ZFSet.{u}) (n : Nat) :
    textbookDStageZF a 0 n = textbookDZeroZF a n :=
  rfl

@[simp]
theorem mem_textbookDStageZF_succ_iff
    {a r : ZFSet.{u}} {k n : Nat} :
    r ∈ textbookDStageZF a (k + 1) n ↔
      r ∈ textbookDStageZF a k n ∨
      (∃ t ∈ textbookDStageZF a k n,
        textbookTupleSpace a n \ t = r) ∨
      (∃ t ∈ textbookDStageZF a k n,
        ∃ v ∈ textbookDStageZF a k n, t ∩ v = r) ∨
      (∃ t ∈ textbookDStageZF a k (n + 1),
        textbookExistsProjZF a n t = r) := by
  simp only [textbookDStageZF, ZFSet.mem_union,
    mem_textbookComplementFamilyZF_iff,
    mem_textbookIntersectionFamilyZF_iff,
    mem_textbookProjectionFamilyZF_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem textbookDStageZF_subset_tupleSpace
    (a : ZFSet.{u}) (k n : Nat) :
    ∀ r ∈ textbookDStageZF a k n, r ⊆ textbookTupleSpace a n := by
  induction k generalizing n with
  | zero =>
      intro r hr
      rcases mem_textbookDZeroZF_iff.mp hr with
        ⟨i, j, h⟩ | ⟨i, j, h⟩
      · rw [← h]
        exact textbookDInZF_subset_tupleSpace a n i.1 j.1
      · rw [← h]
        exact textbookDEqZF_subset_tupleSpace a n i.1 j.1
  | succ k ih =>
      intro r hr
      rcases mem_textbookDStageZF_succ_iff.mp hr with
        hr | ⟨t, ht, htr⟩ | ⟨t, ht, v, hv, htvr⟩ | ⟨t, ht, htr⟩
      · exact ih n r hr
      · rw [← htr]
        intro x hx
        exact (ZFSet.mem_sdiff.mp hx).1
      · rw [← htvr]
        intro x hx
        exact ih n t ht (ZFSet.mem_inter.mp hx).1
      · rw [← htr]
        exact textbookExistsProjZF_subset_tupleSpace a n t

theorem textbookDStageZF_subset_succ
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageZF a k n ⊆ textbookDStageZF a (k + 1) n := by
  intro r hr
  exact mem_textbookDStageZF_succ_iff.mpr (Or.inl hr)

theorem textbookDStageZF_mono
    (a : ZFSet.{u}) {k l n : Nat} (hkl : k ≤ l) :
    textbookDStageZF a k n ⊆ textbookDStageZF a l n := by
  induction l, hkl using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ l _ ih =>
      exact ih.trans (textbookDStageZF_subset_succ a l n)

/-! ## The union of all finite stages -/

/-- The genuine ambient `ZFSet`
`Df(a,n) = union_{k in omega} D(k,a,n)` for a standard Lean `Nat` arity.
This definition alone does not assert that the result belongs to a given
transitive model; that requires the internal enumeration and Replacement. -/
noncomputable def textbookDfZF (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.iUnion fun k : Nat => textbookDStageZF a k n

@[simp]
theorem mem_textbookDfZF_iff {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDfZF a n ↔
      ∃ k : Nat, r ∈ textbookDStageZF a k n := by
  simp [textbookDfZF]

theorem textbookDStageZF_subset_DfZF
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageZF a k n ⊆ textbookDfZF a n := by
  intro r hr
  exact mem_textbookDfZF_iff.mpr ⟨k, hr⟩

theorem textbookDfZF_relations
    (a : ZFSet.{u}) (n : Nat) :
    ∀ r ∈ textbookDfZF a n, r ⊆ textbookTupleSpace a n := by
  intro r hr
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  exact textbookDStageZF_subset_tupleSpace a k n r hk

/-! ## First-order formulas for finite function spaces -/

namespace TextbookDefFormula

/-- The bounded formula saying that `graph` contains `<input, output>`. -/
def graphValueDeltaAt {n : Nat}
    (graph input output : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx graph
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) input.castSucc output.castSucc)

/-- `graph` contains the Kuratowski pair `<input, output>`. -/
def graphValueAt {n : Nat}
    (graph input output : Fin n) : FOFormula n :=
  (graphValueDeltaAt graph input output).toFO

@[simp]
theorem satisfies_graphValueDeltaAt {n : Nat}
    (graph input output : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphValueDeltaAt graph input output) s ↔
      ZFSet.pair (s input) (s output) ∈ s graph := by
  simp only [graphValueDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s input) (s output), hq, rfl⟩

@[simp]
theorem satisfies_graphValueAt {n : Nat}
    (graph input output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (graphValueAt graph input output) s ↔
      ZFSet.pair (s input) (s output) ∈ s graph := by
  rw [graphValueAt, Delta0Formula.satisfies_toFO,
    satisfies_graphValueDeltaAt]

/-- Bounded graph-in-product predicate. -/
def graphBetweenDeltaAt {n : Nat}
    (graph domain codomain : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedAll graph
    (Delta0Formula.boundedEx domain.castSucc
      (Delta0Formula.boundedEx codomain.castSucc.castSucc
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)))))

/-- Every member of `graph` is a pair from `domain × codomain`. -/
def graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  (graphBetweenDeltaAt graph domain codomain).toFO

@[simp]
theorem satisfies_graphBetweenDeltaAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphBetweenDeltaAt graph domain codomain) s ↔
      s graph ⊆ ZFSet.prod (s domain) (s codomain) := by
  simp only [graphBetweenDeltaAt,
    Delta0Formula.satisfies_boundedAll, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · intro h q hq
    rcases h q hq with ⟨x, hx, y, hy, hqPair⟩
    rw [ZFSet.mem_prod]
    exact ⟨x, hx, y, hy, hqPair⟩
  · intro h q hq
    rcases ZFSet.mem_prod.mp (h hq) with ⟨x, hx, y, hy, hqPair⟩
    exact ⟨x, hx, y, hy, hqPair⟩

@[simp]
theorem satisfies_graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (graphBetweenAt graph domain codomain) s ↔
      s graph ⊆ ZFSet.prod (s domain) (s codomain) := by
  rw [graphBetweenAt, Delta0Formula.satisfies_toFO,
    satisfies_graphBetweenDeltaAt]

/-- Bounded uniqueness of the graph value at one input. -/
def uniqueValueDeltaAt {n : Nat}
    (graph input codomain : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx codomain
    (.conj
      (graphValueDeltaAt graph.castSucc input.castSucc (Fin.last n))
      (Delta0Formula.boundedAll codomain.castSucc
        (Delta0Formula.imp
          (graphValueDeltaAt graph.castSucc.castSucc
            input.castSucc.castSucc (Fin.last (n + 1)))
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

/-- At `input`, `graph` has exactly one value, and that value is in `codomain`. -/
def uniqueValueAt {n : Nat}
    (graph input codomain : Fin n) : FOFormula n :=
  (uniqueValueDeltaAt graph input codomain).toFO

@[simp]
theorem satisfies_uniqueValueDeltaAt {n : Nat}
    (graph input codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (uniqueValueDeltaAt graph input codomain) s ↔
      ∃ output ∈ s codomain,
        ZFSet.pair (s input) output ∈ s graph ∧
          ∀ other ∈ s codomain,
            ZFSet.pair (s input) other ∈ s graph → other = output := by
  simp only [uniqueValueDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll, Delta0Formula.satisfies_imp,
    satisfies_graphValueDeltaAt,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_uniqueValueAt {n : Nat}
    (graph input codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (uniqueValueAt graph input codomain) s ↔
      ∃ output ∈ s codomain,
        ZFSet.pair (s input) output ∈ s graph ∧
          ∀ other ∈ s codomain,
            ZFSet.pair (s input) other ∈ s graph → other = output := by
  rw [uniqueValueAt, Delta0Formula.satisfies_toFO,
    satisfies_uniqueValueDeltaAt]

/-- Bounded predicate for a total set-theoretic function. -/
def isFunctionDeltaAt {n : Nat}
    (graph domain codomain : Fin n) : Delta0Formula n :=
  .conj
    (graphBetweenDeltaAt graph domain codomain)
    (Delta0Formula.boundedAll domain
      (uniqueValueDeltaAt graph.castSucc (Fin.last n) codomain.castSucc))

/-- `graph` is a total set-theoretic function from `domain` to `codomain`. -/
def isFunctionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  (isFunctionDeltaAt graph domain codomain).toFO

@[simp]
theorem satisfies_isFunctionDeltaAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (isFunctionDeltaAt graph domain codomain) s ↔
      ZFSet.IsFunc (s domain) (s codomain) (s graph) := by
  simp only [isFunctionDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll,
    satisfies_graphBetweenDeltaAt, satisfies_uniqueValueDeltaAt,
    snoc_last, snoc_castSucc, ZFSet.IsFunc]
  constructor
  · rintro ⟨hsubset, htotal⟩
    refine ⟨hsubset, ?_⟩
    intro input hinput
    rcases htotal input hinput with
      ⟨output, houtput, hpair, hunique⟩
    refine ⟨output, hpair, ?_⟩
    intro other hother
    have hotherCodomain : other ∈ s codomain :=
      (ZFSet.pair_mem_prod.mp (hsubset hother)).2
    exact hunique other hotherCodomain hother
  · rintro ⟨hsubset, htotal⟩
    refine ⟨hsubset, ?_⟩
    intro input hinput
    rcases htotal input hinput with ⟨output, hpair, hunique⟩
    have houtput : output ∈ s codomain :=
      (ZFSet.pair_mem_prod.mp (hsubset hpair)).2
    exact ⟨output, houtput, hpair,
      fun other _hother => hunique other⟩

@[simp]
theorem satisfies_isFunctionAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (isFunctionAt graph domain codomain) s ↔
      ZFSet.IsFunc (s domain) (s codomain) (s graph) := by
  rw [isFunctionAt, Delta0Formula.satisfies_toFO,
    satisfies_isFunctionDeltaAt]

/-- `space` is exactly the set of all functions from `domain` to `codomain`. -/
def functionSpaceAt {n : Nat}
    (space domain codomain : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) space.castSucc)
      (isFunctionAt (Fin.last n) domain.castSucc codomain.castSucc))

@[simp]
theorem satisfies_functionSpaceAt {n : Nat}
    (space domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (functionSpaceAt space domain codomain) s ↔
      s space = ZFSet.funs (s domain) (s codomain) := by
  simp only [functionSpaceAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_isFunctionAt, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    exact h graph
  · intro h graph
    rw [h]
    change graph ∈ ZFSet.funs (s domain) (s codomain) ↔
      ZFSet.IsFunc (s domain) (s codomain) graph
    exact ZFSet.mem_funs

/-- The three-variable graph formula for `(domain,codomain) ↦ codomain^domain`. -/
def functionSpaceGraph : FOFormula 3 :=
  functionSpaceAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_functionSpaceGraph
    (domain codomain space : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem functionSpaceGraph
        ![domain, codomain, space] ↔
      space = ZFSet.funs domain codomain := by
  simp [functionSpaceGraph]

end TextbookDefFormula

end Constructible
