import OneY.ExtractionGeometry

/-!
# Actual inherited-forest extraction and its finite iteration

The top values and the geometric pseudo-parent forest are both computed.
All extraction layers are finite in number on a finite positive input
starting with one; no limit imposed by the web interface is used here.
This is finiteness of building one mountain, not termination of expansion.
-/

namespace OneY.Numeric

def extract (base : Row) (hpos : ∀ c, 0 < base.value c) : Row :=
  rawExtract base hpos

theorem extract_positive (base : Row) (hpos : ∀ c, 0 < base.value c) (c : Nat) :
    0 < (extract base hpos).value c := topValue_pos base (hpos c)

theorem extract_rootsOne (base : Row) (hpos : ∀ c, 0 < base.value c)
    (hroots : base.RootsOne) : (extract base hpos).RootsOne := by
  apply select_rootsOne _ _ (fun c => topValue_pos base (hpos c))
  intro c hp
  have hh := (Pseudo.parent_none_iff (mountain base hpos) c).mp hp
  exact topValue_eq_one_of_height_zero base hpos hroots hh

def RootedRow.extract (a : RootedRow) : RootedRow where
  row := Numeric.extract a.row a.positive
  positive := extract_positive a.row a.positive
  rootsOne := extract_rootsOne a.row a.positive a.rootsOne

theorem RootedRow.extract_value_le (a : RootedRow) (c : Nat) :
    a.extract.row.value c ≤ a.row.value c := topValue_le a.row c

theorem RootedRow.extract_value_lt (a : RootedRow) {c : Nat}
    (hc : 1 < a.row.value c) : a.extract.row.value c < a.row.value c := by
  cases hp : a.row.forest.parent c with
  | none => have h := a.rootsOne c hp; omega
  | some p => exact topValue_lt_of_parent a.row hp

def layers (base : RootedRow) : Nat → RootedRow
  | 0 => base
  | k+1 => (layers base k).extract

theorem layers_value_le (base : RootedRow) (k c : Nat) :
    (layers base (k+1)).row.value c ≤ (layers base k).row.value c :=
  (layers base k).extract_value_le c

theorem layers_value_antitone (base : RootedRow) {k l : Nat} (hkl : k ≤ l)
    (c : Nat) : (layers base l).row.value c ≤ (layers base k).row.value c := by
  induction hkl with
  | refl => exact Nat.le_refl _
  | @step l _ ih => exact Nat.le_trans (layers_value_le base l c) ih

theorem layers_value_budget (base : RootedRow) (k c : Nat)
    (hc : 1 < (layers base k).row.value c) :
    (layers base k).row.value c + k ≤ base.row.value c := by
  induction k with
  | zero => simp only [layers, Nat.add_zero]; exact Nat.le_refl _
  | succ k ih =>
      have hle := layers_value_le base k c
      have hprev : 1 < (layers base k).row.value c := by omega
      have hi := ih hprev
      have hlt := (layers base k).extract_value_lt hprev
      change (layers base (k+1)).row.value c < (layers base k).row.value c at hlt
      omega

theorem layers_one_of_bound (base : RootedRow) {k c : Nat}
    (hk : base.row.value c ≤ k+1) : (layers base k).row.value c = 1 := by
  have hp := (layers base k).positive c
  by_cases hc : 1 < (layers base k).row.value c
  · have h := layers_value_budget base k c hc
    omega
  · omega

def sequenceBound (s : List Nat) : Nat := max 1 (ZeroY.maxValue s)

theorem sequence_value_le_bound (s : List Nat) (c : Nat) :
    (ofSequence s).value c ≤ sequenceBound s := by
  change s[c]?.getD 1 ≤ max 1 (ZeroY.maxValue s)
  cases hv : s[c]? with
  | none => exact Nat.le_max_left _ _
  | some v =>
      simp only [Option.getD_some]
      exact Nat.le_trans (ZeroY.le_maxValue (List.mem_of_getElem? hv)) (Nat.le_max_right _ _)

/-- A uniform, proved stopping bound for the complete extracted mountain. -/
theorem sequence_layers_all_one (s : List Nat) (hs : ZeroY.Legal s) {k : Nat}
    (hk : sequenceBound s ≤ k+1) :
    ∀ c, (layers (rootedSequence s hs) k).row.value c = 1 := by
  intro c
  apply layers_one_of_bound
  exact Nat.le_trans (sequence_value_le_bound s c) hk

theorem sequence_layers_no_parents (s : List Nat) (hs : ZeroY.Legal s) {k : Nat}
    (hk : sequenceBound s ≤ k+1) :
    ∀ c, (layers (rootedSequence s hs) k).row.forest.parent c = none := by
  intro c
  exact Row.parent_none_of_one _ (sequence_layers_all_one s hs hk c)

/-- The finite list of complete numerical layers, including its final
all-one layer. Extra all-one layers would not change any parent graph. -/
def boundedLayers (s : List Nat) (hs : ZeroY.Legal s) : List RootedRow :=
  (List.range (sequenceBound s)).map (layers (rootedSequence s hs))

def rowDone (n : Nat) (a : RootedRow) : Bool :=
  (List.range n).all fun c => a.row.value c = 1

/-- Stop at the first all-one layer, keeping that final layer. -/
def completeLayers (s : List Nat) (hs : ZeroY.Legal s) : List RootedRow :=
  let xs := boundedLayers s hs
  xs.take (xs.findIdx (rowDone s.length) + 1)

end OneY.Numeric

#print axioms OneY.Numeric.extract_rootsOne
#print axioms OneY.Numeric.layers_one_of_bound
#print axioms OneY.Numeric.sequence_layers_no_parents
