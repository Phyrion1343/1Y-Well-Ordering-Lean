import OneY.Extraction

/-!
# Existence of a bad root for every non-successor column

This closes a totality obligation of the numerical algorithm: building the
mountain cannot exhaust its layers before a difference-one parent is found.
-/

namespace OneY.Numeric

theorem layers_extract (a : RootedRow) (k : Nat) :
    layers a.extract k = layers a (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg RootedRow.extract ih

def BadAt (a : RootedRow) (k r c p : Nat) : Prop :=
  (rows (layers a k).row r).forest.parent c = some p ∧
    (rows (layers a k).row r).value c =
      (rows (layers a k).row r).value p + 1

theorem badAt_of_top_one (a : RootedRow) {c : Nat}
    (hc : 1 < a.row.value c) (ht : topValue a.row c = 1) :
    ∃ r p, BadAt a 0 r c p := by
  have hh : 0 < height a.row c := by
    cases hp : a.row.forest.parent c with
    | none => have h := a.rootsOne c hp; omega
    | some p => exact (parent_exists_iff_lt_height a.row (a.positive c) 0).mp ⟨p, hp⟩
  let r := height a.row c - 1
  have hr : r+1 = height a.row c := by dsimp [r]; omega
  obtain ⟨p, hp⟩ := (parent_exists_iff_lt_height a.row (a.positive c) r).mpr (by omega)
  have ht' : (rows a.row (r+1)).value c = 1 := by
    simpa only [hr, topValue] using ht
  change (rows a.row r).difference c = 1 at ht'
  simp only [Row.difference, hp] at ht'
  have hv := (rows a.row r).parent_values hp
  refine ⟨r, p, hp, ?_⟩
  change (rows a.row r).value c = (rows a.row r).value p + 1
  omega

theorem exists_badAt (a : RootedRow) (c : Nat) (hc : 1 < a.row.value c) :
    ∃ k r p, BadAt a k r c p := by
  generalize hv : a.row.value c = v at hc
  induction v using Nat.strongRecOn generalizing a with
  | ind v ih =>
      by_cases ht : topValue a.row c = 1
      · obtain ⟨r, p, hp⟩ := badAt_of_top_one a (by omega) ht
        exact ⟨0, r, p, hp⟩
      · have hpos := topValue_pos a.row (a.positive c)
        have htop : 1 < a.extract.row.value c := by
          change 1 < topValue a.row c
          omega
        have hlt := a.extract_value_lt (c := c) (by omega)
        obtain ⟨k, r, p, hp⟩ := ih (a.extract.row.value c) (by omega) a.extract rfl htop
        refine ⟨k+1, r, p, ?_⟩
        simpa only [BadAt, layers_extract] using hp

theorem badAt_value_gt_one {a : RootedRow} {k r c p : Nat}
    (h : BadAt a k r c p) : 1 < (layers a k).row.value c := by
  have hp := (rows (layers a k).row r).parent_values h.1
  have hle := rows_value_antitone (layers a k).row (Nat.zero_le r) c
  have he := h.2
  change (rows (layers a k).row r).value c ≤ (layers a k).row.value c at hle
  omega

theorem badAt_layer_bound {a : RootedRow} {k r c p : Nat}
    (h : BadAt a k r c p) : k + 2 ≤ a.row.value c := by
  have hgt := badAt_value_gt_one h
  have hbudget := layers_value_budget a k c hgt
  omega

theorem badAt_row_bound {a : RootedRow} {k r c p : Nat}
    (h : BadAt a k r c p) : r < height (layers a k).row c :=
  (parent_exists_iff_lt_height _ ((layers a k).positive c) r).mp ⟨p, h.1⟩

theorem badAt_height_and_top {a : RootedRow} {k r c p : Nat}
    (h : BadAt a k r c p) :
    height (layers a k).row c = r+1 ∧ topValue (layers a k).row c = 1 := by
  have hv : (rows (layers a k).row (r+1)).value c = 1 := by
    change (rows (layers a k).row r).difference c = 1
    simp only [Row.difference, h.1, h.2]
    omega
  have hnp := Row.parent_none_of_one (rows (layers a k).row (r+1)) hv
  have hlo := (live_iff_le_height (layers a k).row ((layers a k).positive c) (r+1)).mp
    (by omega : 0 < (rows (layers a k).row (r+1)).value c)
  have hhi : height (layers a k).row c ≤ r+1 := by
    by_cases hn : r+1 < height (layers a k).row c
    · obtain ⟨q, hq⟩ := (parent_exists_iff_lt_height _ ((layers a k).positive c) (r+1)).mpr hn
      rw [hnp] at hq
      contradiction
    · omega
  have he : height (layers a k).row c = r+1 := by omega
  exact ⟨he, by simpa only [topValue, he] using hv⟩

theorem badAt_next_layer_one {a : RootedRow} {k r c p : Nat}
    (h : BadAt a k r c p) : (layers a (k+1)).row.value c = 1 :=
  (badAt_height_and_top h).2

theorem badAt_unique {a : RootedRow} {k r c p l s q : Nat}
    (h : BadAt a k r c p) (h' : BadAt a l s c q) : k = l ∧ r = s ∧ p = q := by
  have hk : k = l := by
    have hnext := badAt_next_layer_one h
    have hnext' := badAt_next_layer_one h'
    have hg := badAt_value_gt_one h
    have hg' := badAt_value_gt_one h'
    by_cases hkl : k < l
    · have hle := layers_value_antitone a (by omega : k+1 ≤ l) c
      omega
    · by_cases hlk : l < k
      · have hle := layers_value_antitone a (by omega : l+1 ≤ k) c
        omega
      · omega
  subst l
  have hh := (badAt_height_and_top h).1
  have hh' := (badAt_height_and_top h').1
  have hrs : r = s := by omega
  subst s
  have he : some p = some q := h.1.symm.trans h'.1
  exact ⟨rfl, rfl, Option.some.inj he⟩

theorem sequence_badRoot_exists (s : List Nat) (hs : ZeroY.Legal s) (c : Nat)
    (hc : (ofSequence s).forest.parent c ≠ none) :
    ∃ k, k < sequenceBound s ∧ ∃ r p,
      r < height (layers (rootedSequence s hs) k).row c ∧
      BadAt (rootedSequence s hs) k r c p := by
  have hpos := ofSequence_positive s hs.1 c
  have hgt : 1 < (ofSequence s).value c := by
    by_cases he : (ofSequence s).value c = 1
    · exact False.elim (hc (Row.parent_none_of_one _ he))
    · omega
  obtain ⟨k, r, p, h⟩ := exists_badAt (rootedSequence s hs) c hgt
  have hk := badAt_layer_bound h
  have hbound := sequence_value_le_bound s c
  change k + 2 ≤ (ofSequence s).value c at hk
  exact ⟨k, by omega, r, p, badAt_row_bound h, h⟩

end OneY.Numeric

#print axioms OneY.Numeric.exists_badAt
#print axioms OneY.Numeric.sequence_badRoot_exists
