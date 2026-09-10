import OneY.NumericRoots
import OneY.Pseudo

/-!
# Extraction and the finite mountain geometry

The extracted row keeps the geometric pseudo-parent forest as its candidate
forest. Its actual parents are computed by the same positive, nearest-smaller
selection as every numerical row. A selected parent has strictly smaller
height in the mountain from which it was extracted.
-/

namespace OneY.Numeric

/-- One extraction, retaining the candidate relation supplied by the legs. -/
def rawExtract (base : Row) (hpos : ∀ c, 0 < base.value c) : Row :=
  select (Pseudo.forest (mountain base hpos)) (topValue base)

theorem rawExtract_positive (base : Row) (hpos : ∀ c, 0 < base.value c)
    (c : Nat) : 0 < (rawExtract base hpos).value c :=
  topValue_pos base (hpos c)

/-- Two tops of equal height on a pseudo-ancestor chain occur in the same
last finite candidate forest. The absence of a parent at the top forces
the earlier top to have at least the value of the later one. -/
theorem topValue_le_of_same_height_pseudo_ancestor
    (base : Row) (hpos : ∀ c, 0 < base.value c) {p c : Nat}
    (ha : (Pseudo.forest (mountain base hpos)).Ancestor p c)
    (heq : height base p = height base c) :
    topValue base c ≤ topValue base p := by
  have hrow := Pseudo.same_height_ancestor (mountain base hpos) ha heq
  change (rows base (height base c - 1)).forest.Ancestor p c at hrow
  have hn := top_parent_none base (hpos c)
  by_cases hz : height base c = 0
  · rw [hz, Nat.zero_sub] at hrow
    rw [hz] at hn
    cases hrow with
    | direct hp => rw [hn] at hp; contradiction
    | step _ hp => rw [hn] at hp; contradiction
  · have hs : height base c = (height base c - 1) + 1 := by omega
    have hrows : rows base (height base c) =
        (rows base (height base c - 1)).next := by
      conv => lhs; rw [hs]
      rfl
    rw [hrows] at hn
    have hpv : 0 < (rows base (height base c - 1)).difference p := by
      have hp := topValue_pos base (hpos p)
      simpa only [topValue, heq, hrows, Row.next_value] using hp
    have hle := (restrictedParent_none_iff
      (rows base (height base c - 1)).forest
      (rows base (height base c - 1)).difference c).mp hn p hrow hpv
    simpa only [topValue, heq, hrows, Row.next_value] using hle

theorem rawExtract_parent_height_lt (base : Row)
    (hpos : ∀ c, 0 < base.value c) {c p : Nat}
    (hp : (rawExtract base hpos).forest.parent c = some p) :
    height base p < height base c := by
  have hspec := restrictedParent_spec
    (Pseudo.forest (mountain base hpos)) (topValue base) hp
  have ha := ParentForest.ancestor_of_zeroY hspec.1
  have hle := Pseudo.ancestor_height_le (mountain base hpos) ha
  change height base p ≤ height base c at hle
  by_cases heq : height base p = height base c
  · have hanti := topValue_le_of_same_height_pseudo_ancestor base hpos ha heq
    have hstrict := hspec.2.2
    omega
  · omega

theorem rawExtract_ancestor_height_lt (base : Row)
    (hpos : ∀ c, 0 < base.value c) {a c : Nat}
    (ha : (rawExtract base hpos).forest.Ancestor a c) :
    height base a < height base c := by
  induction ha with
  | direct hp => exact rawExtract_parent_height_lt base hpos hp
  | step _ hp ih =>
      exact Nat.lt_trans ih (rawExtract_parent_height_lt base hpos hp)

end OneY.Numeric

#print axioms OneY.Numeric.topValue_le_of_same_height_pseudo_ancestor
#print axioms OneY.Numeric.rawExtract_parent_height_lt
#print axioms OneY.Numeric.rawExtract_ancestor_height_lt
