import OneY.NumericGeometry

/-! # Root values and the invariant needed for iterated extraction -/

namespace OneY.Numeric

open ZeroY YesMetaZFC.BMS

theorem restrictedParent_none_iff (frame : ParentForest) (value : Nat → Nat)
    (c : Nat) : restrictedParent frame value c = none ↔
    ∀ p, frame.Ancestor p c → 0 < value p → value c ≤ value p := by
  unfold restrictedParent
  rw [greatestBelow?_eq_none_iff]
  constructor
  · intro hn p ha hp
    have hlt := ha.lt
    have hm := (ZeroY.Forest.ancestorChain_contains_iff frame.parent_left).mpr
      (ParentForest.ancestor_to_zeroY ha)
    have h := hn p hlt
    by_cases hv : value p < value c
    · have ht : ((ancestorChain frame.parent c c).contains p &&
          (decide (0 < value p) && decide (value p < value c))) = true := by
        simp only [hm, hp, hv, decide_true, Bool.true_and]
      rw [ht] at h
      contradiction
    · omega
  · intro hn p _
    by_cases ha : frame.Ancestor p c
    · have hm := (ZeroY.Forest.ancestorChain_contains_iff frame.parent_left).mpr
        (ParentForest.ancestor_to_zeroY ha)
      by_cases hp : 0 < value p
      · have hle := hn p ha hp
        simp only [hm, hp, Nat.not_lt.mpr hle, decide_true, decide_false,
          Bool.true_and]
      · simp only [hm, hp, decide_false, Bool.false_and, Bool.true_and]
    · have hm : (ancestorChain frame.parent c c).contains p = false := by
        cases ht : (ancestorChain frame.parent c c).contains p with
        | false => rfl
        | true =>
            exact False.elim (ha (ParentForest.ancestor_of_zeroY
              ((ZeroY.Forest.ancestorChain_contains_iff frame.parent_left).mp ht)))
      simp only [hm, Bool.false_and]

theorem Row.parent_none_of_one (a : Row) {c : Nat} (hc : a.value c = 1) :
    a.forest.parent c = none := by
  cases hp : a.forest.parent c with
  | none => rfl
  | some p => have hv := a.parent_values hp; omega

def Row.RootsOne (a : Row) : Prop :=
  ∀ c, a.forest.parent c = none → a.value c = 1

theorem select_rootsOne (frame : ParentForest) (value : Nat → Nat)
    (hpos : ∀ c, 0 < value c)
    (hroots : ∀ c, frame.parent c = none → value c = 1) :
    (select frame value).RootsOne := by
  intro c hn
  change value c = 1
  have hroot := hroots (frame.root c) (frame.parent_root c)
  rcases frame.root_ancestor_or_eq c with ha | he
  · have hle := (restrictedParent_none_iff frame value c).mp hn
      (frame.root c) ha (hpos _)
    have hc := hpos c
    omega
  · simpa only [he] using hroot

theorem Row.parent_none_iff_one (a : Row) (ha : a.RootsOne) (c : Nat) :
    a.forest.parent c = none ↔ a.value c = 1 :=
  ⟨ha c, a.parent_none_of_one⟩

theorem ofSequence_rootsOne (s : List Nat) (hs : ZeroY.Legal s) :
    (ofSequence s).RootsOne := by
  apply select_rootsOne linearForest (fun c => s[c]?.getD 1)
  · exact ofSequence_positive s hs.1
  · intro c hp
    cases c with
    | zero =>
        rcases hs.2 with he | hh
        · simp [he]
        · cases s with
          | nil => simp
          | cons v vs => simpa using hh
    | succ c => simp [linearForest, ZeroY.linearParent] at hp

theorem topValue_eq_one_of_height_zero (base : Row) (hpos : ∀ c, 0 < base.value c)
    (hroots : base.RootsOne) {c : Nat} (hc : height base c = 0) :
    topValue base c = 1 := by
  have hn := top_parent_none base (hpos c)
  rw [hc] at hn
  change base.forest.parent c = none at hn
  simpa [topValue, hc, rows] using hroots c hn

/-- These are checked input invariants, not a well-foundedness assumption. -/
structure RootedRow where
  row : Row
  positive : ∀ c, 0 < row.value c
  rootsOne : row.RootsOne

def rootedSequence (s : List Nat) (hs : ZeroY.Legal s) : RootedRow :=
  ⟨ofSequence s, ofSequence_positive s hs.1, ofSequence_rootsOne s hs⟩

end OneY.Numeric

#print axioms OneY.Numeric.select_rootsOne
#print axioms OneY.Numeric.ofSequence_rootsOne
