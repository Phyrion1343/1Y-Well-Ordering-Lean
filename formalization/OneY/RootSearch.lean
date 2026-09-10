import OneY.Build

/-! # An executable bad-root search with proved totality -/

namespace OneY.Numeric

structure RootAddress where
  layer : Nat
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def rowRoot (a : RootedRow) (k r c : Nat) : Option RootAddress :=
  match (rows (layers a k).row r).forest.parent c with
  | none => none
  | some p =>
      if (rows (layers a k).row r).value c = (rows (layers a k).row r).value p + 1
      then some ⟨k, r, p⟩ else none

theorem rowRoot_spec (a : RootedRow) (k r c : Nat) (z : RootAddress) :
    rowRoot a k r c = some z ↔
      z.layer = k ∧ z.row = r ∧ BadAt a k r c z.column := by
  unfold rowRoot BadAt
  cases hp : (rows (layers a k).row r).forest.parent c with
  | none => simp
  | some p =>
      by_cases hd : (rows (layers a k).row r).value c =
          (rows (layers a k).row r).value p + 1
      · simp only [hd, ↓reduceIte, Option.some.injEq]
        constructor
        · intro hz; subst z; exact ⟨rfl, rfl, rfl, rfl⟩
        · rintro ⟨hl, hr, hc, _⟩
          cases z
          simp_all
      · simp only [hd, ↓reduceIte, Option.some.injEq, reduceCtorEq, false_iff]
        rintro ⟨_, _, hc, he⟩
        exact hd (by simpa only [hc] using he)

def rootCandidates (a : RootedRow) (bound c : Nat) : List RootAddress :=
  (List.range bound).flatMap fun k =>
    (List.range (height (layers a k).row c)).filterMap fun r => rowRoot a k r c

theorem mem_rootCandidates (a : RootedRow) (bound c : Nat) (z : RootAddress) :
    z ∈ rootCandidates a bound c ↔
      z.layer < bound ∧ BadAt a z.layer z.row c z.column := by
  simp only [rootCandidates, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, r, _, hz⟩
    obtain ⟨hl, hr, hb⟩ := (rowRoot_spec a k r c z).mp hz
    exact ⟨by omega, by simpa only [hl, hr] using hb⟩
  · rintro ⟨hk, hb⟩
    exact ⟨z.layer, hk, z.row, badAt_row_bound hb,
      (rowRoot_spec a z.layer z.row c z).mpr ⟨rfl, rfl, hb⟩⟩

def findBadRoot (s : List Nat) (hs : ZeroY.Legal s) (c : Nat) : Option RootAddress :=
  (rootCandidates (rootedSequence s hs) (sequenceBound s) c).head?

theorem findBadRoot_sound (s : List Nat) (hs : ZeroY.Legal s) (c : Nat)
    {z : RootAddress} (hz : findBadRoot s hs c = some z) :
    z.layer < sequenceBound s ∧ BadAt (rootedSequence s hs) z.layer z.row c z.column :=
  (mem_rootCandidates _ _ _ z).mp (List.mem_of_head? hz)

/-- A column has at most one difference-one cell anywhere in the tower,
so the search result is independent of traversal choices. -/
theorem rootAddress_unique {a : RootedRow} {c : Nat} {z w : RootAddress}
    (hz : BadAt a z.layer z.row c z.column)
    (hw : BadAt a w.layer w.row c w.column) : z = w := by
  obtain ⟨hk, hr, hc⟩ := badAt_unique hz hw
  cases z
  cases w
  simp_all

theorem findBadRoot_none_iff (s : List Nat) (hs : ZeroY.Legal s) (c : Nat) :
    findBadRoot s hs c = none ↔ (ofSequence s).forest.parent c = none := by
  constructor
  · intro hn
    by_cases hp : (ofSequence s).forest.parent c = none
    · exact hp
    · obtain ⟨k, hk, r, p, _, hb⟩ := sequence_badRoot_exists s hs c hp
      have hm := (mem_rootCandidates (rootedSequence s hs) (sequenceBound s) c
        ⟨k, r, p⟩).mpr ⟨hk, hb⟩
      have he := List.head?_eq_none_iff.mp hn
      rw [he] at hm
      contradiction
  · intro hp
    have hone := ofSequence_rootsOne s hs c hp
    have he : rootCandidates (rootedSequence s hs) (sequenceBound s) c = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have hb := (mem_rootCandidates _ _ _ z).mp hz
      have hgt := badAt_value_gt_one hb.2
      have hle := layers_value_antitone (rootedSequence s hs) (Nat.zero_le z.layer) c
      change (layers (rootedSequence s hs) z.layer).row.value c ≤
        (ofSequence s).value c at hle
      omega
    simp only [findBadRoot, he, List.head?_nil]

end OneY.Numeric

#print axioms OneY.Numeric.findBadRoot_sound
#print axioms OneY.Numeric.findBadRoot_none_iff
