import OneY.Forest
import ZeroY.Forest.Stack

/-!
# Sparse numerical rows of a 1-Y mountain

Zero denotes an absent cell. In particular, an absent candidate is never
eligible as a parent. The inherited forest is retained independently of
the values, so the numerical sequence alone is not the state.
-/

namespace OneY.Numeric

open ZeroY YesMetaZFC.BMS

def restrictedParent (frame : ParentForest) (value : Nat → Nat) (c : Nat) :
    Option Nat :=
  greatestBelow? c fun p =>
    (ancestorChain frame.parent c c).contains p &&
      (0 < value p && value p < value c)

theorem restrictedParent_left (frame : ParentForest) (value : Nat → Nat)
    {c p : Nat} (hp : restrictedParent frame value c = some p) : p < c :=
  greatestBelow?_some_lt hp

theorem restrictedParent_spec (frame : ParentForest) (value : Nat → Nat)
    {c p : Nat} (hp : restrictedParent frame value c = some p) :
    ZeroY.Forest.Ancestor frame.parent c p ∧ 0 < value p ∧ value p < value c := by
  have h := greatestBelow?_some_satisfies hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(ZeroY.Forest.ancestorChain_contains_iff frame.parent_left).mp h.1,
    h.2.1, h.2.2⟩

theorem restrictedParent_some_iff (frame : ParentForest) (value : Nat → Nat)
    (c p : Nat) : restrictedParent frame value c = some p ↔
    ZeroY.Forest.Ancestor frame.parent c p ∧ 0 < value p ∧ value p < value c ∧
      ∀ q, ZeroY.Forest.Ancestor frame.parent c q → 0 < value q →
        value q < value c → q ≤ p := by
  unfold restrictedParent
  rw [greatestBelow?_eq_some_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    ZeroY.Forest.ancestorChain_contains_iff frame.parent_left]
  constructor
  · rintro ⟨_, ⟨ha, hv, hc⟩, hmax⟩
    exact ⟨ha, hv, hc, fun q hq hpos hlt =>
      hmax q (ZeroY.Forest.ancestor_lt frame.parent_left hq) ⟨hq, hpos, hlt⟩⟩
  · rintro ⟨ha, hv, hc, hmax⟩
    exact ⟨ZeroY.Forest.ancestor_lt frame.parent_left ha, ⟨ha, hv, hc⟩,
      fun q _ hq => hmax q hq.1 hq.2.1 hq.2.2⟩

structure Row where
  value : Nat → Nat
  forest : ParentForest
  parent_values : ∀ {c p : Nat}, forest.parent c = some p →
    0 < value p ∧ value p < value c

def select (frame : ParentForest) (value : Nat → Nat) : Row where
  value := value
  forest := ⟨restrictedParent frame value, restrictedParent_left frame value⟩
  parent_values hp := (restrictedParent_spec frame value hp).2

def Row.difference (a : Row) (c : Nat) : Nat :=
  match a.forest.parent c with
  | none => 0
  | some p => a.value c - a.value p

def Row.next (a : Row) : Row := select a.forest a.difference

theorem Row.next_value (a : Row) (c : Nat) :
    a.next.value c = a.difference c := rfl

theorem Row.difference_pos_iff (a : Row) (c : Nat) :
    0 < a.difference c ↔ ∃ p, a.forest.parent c = some p := by
  cases hp : a.forest.parent c with
  | none => simp [difference, hp]
  | some p =>
      have hv := a.parent_values hp
      constructor
      · intro _; exact ⟨p, rfl⟩
      · intro _
        simp only [difference, hp]
        exact Nat.sub_pos_of_lt hv.2

theorem Row.difference_lt (a : Row) {c : Nat} (hc : 0 < a.value c) :
    a.difference c < a.value c := by
  cases hp : a.forest.parent c with
  | none => simpa [difference, hp] using hc
  | some p =>
      have hv := a.parent_values hp
      simp only [difference, hp]
      omega

theorem Row.difference_le (a : Row) (c : Nat) :
    a.difference c ≤ a.value c := by
  cases hp : a.forest.parent c with
  | none => simp [difference, hp]
  | some p => simp [difference, hp]

theorem Row.difference_zero_of_zero (a : Row) {c : Nat} (hc : a.value c = 0) :
    a.difference c = 0 := by
  have h := a.difference_le c
  omega

def rows (base : Row) : Nat → Row
  | 0 => base
  | r+1 => (rows base r).next

theorem rows_value_le (base : Row) (r c : Nat) :
    (rows base (r+1)).value c ≤ (rows base r).value c :=
  (rows base r).difference_le c

theorem rows_value_antitone (base : Row) {r s : Nat} (hrs : r ≤ s) (c : Nat) :
    (rows base s).value c ≤ (rows base r).value c := by
  induction hrs with
  | refl => exact Nat.le_refl _
  | @step s _ ih => exact Nat.le_trans (rows_value_le base s c) ih

/-- Every live cell has consumed at least its row number from its original
positive value. Thus no artificial row limit is needed. -/
theorem rows_value_budget (base : Row) (r c : Nat)
    (hc : 0 < (rows base r).value c) :
    (rows base r).value c + r ≤ base.value c := by
  induction r with
  | zero => simp only [rows, Nat.add_zero]; exact Nat.le_refl _
  | succ r ih =>
      have hle := rows_value_le base r c
      have hprev : 0 < (rows base r).value c := by omega
      have hi := ih hprev
      have hstrict := (rows base r).difference_lt hprev
      change (rows base (r+1)).value c < (rows base r).value c at hstrict
      omega

theorem rows_zero_of_bound (base : Row) {r c : Nat} (hr : base.value c ≤ r) :
    (rows base r).value c = 0 := by
  by_cases hc : 0 < (rows base r).value c
  · have h := rows_value_budget base r c hc
    omega
  · omega

theorem rows_parent_iff_next_live (base : Row) (r c : Nat) :
    (∃ p, (rows base r).forest.parent c = some p) ↔
      0 < (rows base (r+1)).value c :=
  ((rows base r).difference_pos_iff c).symm

/-- The last live row is searched within a bound already proved sufficient. -/
def topSearch (base : Row) (c : Nat) : Option Nat :=
  greatestBelow? (base.value c) fun r => 0 < (rows base r).value c

def height (base : Row) (c : Nat) : Nat := (topSearch base c).getD 0

theorem topSearch_some (base : Row) {c : Nat} (hc : 0 < base.value c) :
    topSearch base c = some (height base c) := by
  cases ht : topSearch base c with
  | none =>
      have hn := greatestBelow?_eq_none_iff.mp ht 0 hc
      have hy : decide (0 < (rows base 0).value c) = true := decide_eq_true hc
      rw [hy] at hn
      contradiction
  | some r => simp only [height, ht, Option.getD_some]

theorem height_live (base : Row) {c : Nat} (hc : 0 < base.value c) :
    0 < (rows base (height base c)).value c := by
  have h := greatestBelow?_some_satisfies (topSearch_some base hc)
  exact of_decide_eq_true h

theorem height_lt (base : Row) {c : Nat} (hc : 0 < base.value c) :
    height base c < base.value c :=
  greatestBelow?_some_lt (topSearch_some base hc)

theorem live_iff_le_height (base : Row) {c : Nat} (hc : 0 < base.value c)
    (r : Nat) : 0 < (rows base r).value c ↔ r ≤ height base c := by
  constructor
  · intro hr
    have hbudget := rows_value_budget base r c hr
    have hmax := (greatestBelow?_eq_some_iff.mp (topSearch_some base hc)).2.2
    exact hmax r (by omega) (decide_eq_true hr)
  · intro hr
    have hlive := height_live base hc
    have hle := rows_value_antitone base hr c
    omega

theorem parent_exists_iff_lt_height (base : Row) {c : Nat}
    (hc : 0 < base.value c) (r : Nat) :
    (∃ p, (rows base r).forest.parent c = some p) ↔ r < height base c := by
  rw [rows_parent_iff_next_live, live_iff_le_height base hc]
  omega

theorem parent_endpoint (base : Row) (hbase : ∀ c, 0 < base.value c)
    {r c p : Nat} (hp : (rows base r).forest.parent c = some p) :
    r ≤ height base p :=
  (live_iff_le_height base (hbase p) r).mp ((rows base r).parent_values hp).1

theorem top_parent_none (base : Row) {c : Nat} (hc : 0 < base.value c) :
    (rows base (height base c)).forest.parent c = none := by
  cases hp : (rows base (height base c)).forest.parent c with
  | none => rfl
  | some p =>
      have h := (parent_exists_iff_lt_height base hc (height base c)).mp ⟨p, hp⟩
      omega

def topValue (base : Row) (c : Nat) : Nat :=
  (rows base (height base c)).value c

theorem topValue_pos (base : Row) {c : Nat} (hc : 0 < base.value c) :
    0 < topValue base c := height_live base hc

theorem topValue_le (base : Row) (c : Nat) : topValue base c ≤ base.value c :=
  rows_value_antitone base (Nat.zero_le _) c

theorem topValue_lt_of_parent (base : Row) {c p : Nat}
    (hp : base.forest.parent c = some p) : topValue base c < base.value c := by
  have hpos : 0 < base.value c := Nat.lt_trans (base.parent_values hp).1
    (base.parent_values hp).2
  have hh : 0 < height base c :=
    (parent_exists_iff_lt_height base hpos 0).mp ⟨p, hp⟩
  have hle := rows_value_antitone base (by omega : 1 ≤ height base c) c
  have hlt := base.difference_lt hpos
  exact Nat.lt_of_le_of_lt hle hlt

theorem topValue_eq_of_no_parent (base : Row) {c : Nat}
    (hc : 0 < base.value c) (hp : base.forest.parent c = none) :
    topValue base c = base.value c := by
  have hh : height base c = 0 := by
    by_cases h : 0 < height base c
    · obtain ⟨p, hp'⟩ := (parent_exists_iff_lt_height base hc 0).mpr h
      change base.forest.parent c = some p at hp'
      rw [hp] at hp'
      contradiction
    · omega
  simp [topValue, hh, rows]

end OneY.Numeric

#print axioms OneY.Numeric.restrictedParent_some_iff
#print axioms OneY.Numeric.rows_zero_of_bound
#print axioms OneY.Numeric.live_iff_le_height
#print axioms OneY.Numeric.topValue_lt_of_parent
