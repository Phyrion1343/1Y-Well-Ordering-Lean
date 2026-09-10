import OneY.SparseComparison

/-! # Comparison by the finite depth suffix followed by the top value -/

namespace OneY.Numeric

theorem rows_next (base : Row) (r : Nat) : rows base.next r = rows base (r+1) := by
  induction r with
  | zero => rfl
  | succ r ih => change (rows base.next r).next = (rows base (r+1)).next; rw [ih]

theorem Row.parent_none_of_value_zero (base : Row) {c : Nat} (hc : base.value c = 0) :
    base.forest.parent c = none := by
  cases hp : base.forest.parent c with
  | none => rfl
  | some p => have := base.parent_values hp; omega

theorem rows_value_zero_of_parent_none (base : Row) {c : Nat}
    (hp : base.forest.parent c = none) (r : Nat) : (rows base (r+1)).value c = 0 := by
  have hz : (rows base 1).value c = 0 := by change base.difference c = 0; simp [Row.difference, hp]
  have hle := rows_value_antitone base (by omega : 1 ≤ r+1) c
  omega

theorem rows_depth_zero_of_parent_none (base : Row) {c : Nat}
    (hp : base.forest.parent c = none) (r : Nat) : (rows base r).forest.depth c = 0 := by
  cases r with
  | zero => exact base.forest.depth_of_parent_none hp
  | succ r =>
      exact (rows base (r+1)).forest.depth_of_parent_none
        ((rows base (r+1)).parent_none_of_value_zero (rows_value_zero_of_parent_none base hp r))

theorem height_next_of_parent (base : Row) {c p : Nat}
    (hp : base.forest.parent c = some p) : height base c = height base.next c+1 := by
  have hpos : 0 < base.value c := by have := base.parent_values hp; omega
  have hnpos : 0 < base.next.value c := (base.difference_pos_iff c).mpr ⟨p, hp⟩
  have hlive := height_live base.next hnpos
  rw [rows_next] at hlive
  have hle := (live_iff_le_height base hpos _).mp hlive
  have hold := height_live base hpos
  have hShift : rows base.next (height base c-1) = rows base (height base c) := by
    rw [rows_next, Nat.sub_add_cancel (by omega : 1 ≤ height base c)]
  rw [← hShift] at hold
  have hge := (live_iff_le_height base.next hnpos _).mp hold
  omega

theorem topValue_next_of_parent (base : Row) {c p : Nat}
    (hp : base.forest.parent c = some p) : topValue base.next c = topValue base c := by
  unfold topValue
  rw [rows_next, ← height_next_of_parent base hp]

def DepthsEqual (base : Row) (left right : Nat) : Prop :=
  ∀ r, (rows base r).forest.depth left = (rows base r).forest.depth right

def DepthsLexLT (base : Row) (left right : Nat) : Prop :=
  ∃ r, (∀ i, i < r → (rows base i).forest.depth left = (rows base i).forest.depth right) ∧
    (rows base r).forest.depth left < (rows base r).forest.depth right

/-- The top value is compared only after *all* finite depth coordinates. -/
def KeyLT (base : Row) (left right : Nat) : Prop :=
  DepthsLexLT base left right ∨
    (DepthsEqual base left right ∧ topValue base left < topValue base right)

def KeyEQ (base : Row) (left right : Nat) : Prop :=
  DepthsEqual base left right ∧ topValue base left = topValue base right

/-- The functional depth suffix has a proved finite zero tail; the top value
is consequently a separate final coordinate, never inserted at a local zero. -/
theorem rows_depth_zero_of_bound (base : Row) {c r : Nat}
    (hr : base.value c ≤ r) : (rows base r).forest.depth c = 0 :=
  (rows base r).forest.depth_of_parent_none
    ((rows base r).parent_none_of_value_zero (rows_zero_of_bound base hr))

theorem height_eq_of_depthsEqual (base : Row) {left right : Nat}
    (hL : 0 < base.value left) (hR : 0 < base.value right)
    (hDepth : DepthsEqual base left right) : height base left = height base right := by
  have hLeftZero := (rows base (height base left)).forest.depth_of_parent_none
    (top_parent_none base hL)
  have hRightZero := (rows base (height base right)).forest.depth_of_parent_none
    (top_parent_none base hR)
  have hRightNone := ((rows base (height base left)).forest.depth_zero_iff right).mp
    ((hDepth _).symm.trans hLeftZero)
  have hLeftNone := ((rows base (height base right)).forest.depth_zero_iff left).mp
    ((hDepth _).trans hRightZero)
  by_cases hLR : height base left < height base right
  · obtain ⟨p, hp⟩ := (parent_exists_iff_lt_height base hR _).mpr hLR
    rw [hRightNone] at hp
    cases hp
  · by_cases hRL : height base right < height base left
    · obtain ⟨p, hp⟩ := (parent_exists_iff_lt_height base hL _).mpr hRL
      rw [hLeftNone] at hp
      cases hp
    · omega

theorem depthsEqual_next (base : Row) {left right : Nat}
    (hZero : base.forest.depth left = base.forest.depth right)
    (hNext : DepthsEqual base.next left right) : DepthsEqual base left right := by
  intro r
  cases r with
  | zero => exact hZero
  | succ r => simpa only [rows_next] using hNext r

theorem keyLT_of_next (base : Row) {left right p : Nat}
    (hZero : base.forest.depth left = base.forest.depth right)
    (hL : base.forest.parent left = some p) (hR : base.forest.parent right = some p)
    (hNext : KeyLT base.next left right) : KeyLT base left right := by
  rcases hNext with ⟨r, hBefore, hLess⟩ | ⟨hEqual, hTop⟩
  · refine Or.inl ⟨r+1, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact hZero
      | succ i => simpa only [rows_next] using hBefore i (by omega)
    · simpa only [rows_next] using hLess
  · exact Or.inr ⟨depthsEqual_next base hZero hEqual,
      by simpa only [topValue_next_of_parent base hL, topValue_next_of_parent base hR] using hTop⟩

theorem keyLT_of_common_chain_value_lt (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p)
    (hValue : v left < v right) : KeyLT (select F v) left right := by
  generalize hSize : v left = size
  induction size using Nat.strongRecOn generalizing F v with
  | ind size ih =>
      obtain ⟨hDepth, hParentOfEq⟩ := select_common_chain_depth_compare F v hL hR hChain
        (Nat.le_of_lt hValue)
      rcases Nat.eq_or_lt_of_le hDepth with hEq | hLess
      · have hParent := hParentOfEq hEq
        cases hp : restrictedParent F v left with
        | none =>
            have hpR := hParent.symm.trans hp
            refine Or.inr ⟨fun r => ?_, ?_⟩
            · rw [rows_depth_zero_of_parent_none (select F v) hp r,
                rows_depth_zero_of_parent_none (select F v) hpR r]
            · rw [topValue_eq_of_no_parent (select F v) hL hp,
                topValue_eq_of_no_parent (select F v) hR hpR]
              exact hValue
        | some p =>
            have hpR := hParent.symm.trans hp
            let a := select F v
            have hAP : a.forest.parent left = some p := hp
            have hAPR : a.forest.parent right = some p := hpR
            have hnL : 0 < a.difference left := (a.difference_pos_iff left).mpr ⟨p, hAP⟩
            have hnR : 0 < a.difference right := (a.difference_pos_iff right).mpr ⟨p, hAPR⟩
            have hSmall : a.difference left < size := by
              have ht := a.difference_lt hL
              change a.difference left < v left at ht
              omega
            have hLessNext : a.difference left < a.difference right := by
              have hpVal := a.parent_values hAP
              simp only [Row.difference, hAP, hAPR]
              change v left-v p < v right-v p
              change 0 < v p ∧ v p < v left at hpVal
              omega
            have hn := ih _ hSmall a.forest a.difference hnL hnR
              (ZeroY.Forest.ancestor_iff_of_parent_eq (show a.forest.parent left = a.forest.parent right from hParent))
              hLessNext rfl
            exact keyLT_of_next a hEq hAP hAPR hn
      · exact Or.inl ⟨0, by intro i hi; omega, hLess⟩

theorem keyEQ_of_common_chain_value_eq (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p)
    (hValue : v left = v right) : KeyEQ (select F v) left right := by
  generalize hSize : v left = size
  induction size using Nat.strongRecOn generalizing F v with
  | ind size ih =>
      obtain ⟨hLR, hParentOfEq⟩ := select_common_chain_depth_compare F v hL hR hChain
        (Nat.le_of_eq hValue)
      have hRL := (select_common_chain_depth_compare F v hR hL
        (fun p => (hChain p).symm) (Nat.le_of_eq hValue.symm)).1
      have hEq := Nat.le_antisymm hLR hRL
      have hParent := hParentOfEq hEq
      cases hp : restrictedParent F v left with
      | none =>
          have hpR := hParent.symm.trans hp
          refine ⟨fun r => ?_, ?_⟩
          · rw [rows_depth_zero_of_parent_none (select F v) hp r,
              rows_depth_zero_of_parent_none (select F v) hpR r]
          · rw [topValue_eq_of_no_parent (select F v) hL hp,
              topValue_eq_of_no_parent (select F v) hR hpR]
            exact hValue
      | some p =>
          have hpR := hParent.symm.trans hp
          let a := select F v
          have hAP : a.forest.parent left = some p := hp
          have hAPR : a.forest.parent right = some p := hpR
          have hnL : 0 < a.difference left := (a.difference_pos_iff left).mpr ⟨p, hAP⟩
          have hnR : 0 < a.difference right := (a.difference_pos_iff right).mpr ⟨p, hAPR⟩
          have hSmall : a.difference left < size := by
            have ht := a.difference_lt hL
            change a.difference left < v left at ht
            omega
          have hNextEq : a.difference left = a.difference right := by
            simp only [Row.difference, hAP, hAPR]
            change v left-v p = v right-v p
            rw [hValue]
          obtain ⟨hDepthNext, hTopNext⟩ := ih _ hSmall a.forest a.difference hnL hnR
            (ZeroY.Forest.ancestor_iff_of_parent_eq (show a.forest.parent left = a.forest.parent right from hParent))
            hNextEq rfl
          change topValue a.next left = topValue a.next right at hTopNext
          exact ⟨depthsEqual_next a hEq hDepthNext,
            by simpa only [topValue_next_of_parent a hAP, topValue_next_of_parent a hAPR] using hTopNext⟩

theorem depthsLexLT_not_equal {base : Row} {left right : Nat}
    (hLt : DepthsLexLT base left right) (hEq : DepthsEqual base left right) : False := by
  obtain ⟨r, _, hr⟩ := hLt
  have := hEq r
  omega

theorem depthsLexLT_asymm {base : Row} {left right : Nat}
    (hLR : DepthsLexLT base left right) (hRL : DepthsLexLT base right left) : False := by
  obtain ⟨r, hBeforeR, hr⟩ := hLR
  obtain ⟨s, hBeforeS, hs⟩ := hRL
  by_cases hRS : r < s
  · have := hBeforeS r hRS; omega
  · by_cases hSR : s < r
    · have := hBeforeR s hSR; omega
    · have he : r = s := by omega
      rw [he] at hr
      omega

theorem keyEQ_symm {base : Row} {left right : Nat}
    (h : KeyEQ base left right) : KeyEQ base right left :=
  ⟨fun r => (h.1 r).symm, h.2.symm⟩

theorem keyLT_not_keyEQ {base : Row} {left right : Nat}
    (hLt : KeyLT base left right) (hEq : KeyEQ base left right) : False := by
  rcases hLt with hDepth | ⟨_, hTop⟩
  · exact depthsLexLT_not_equal hDepth hEq.1
  · have := hEq.2; omega

theorem keyLT_asymm {base : Row} {left right : Nat}
    (hLR : KeyLT base left right) (hRL : KeyLT base right left) : False := by
  rcases hLR with hDepthL | ⟨hEqualL, hTopL⟩
  · rcases hRL with hDepthR | ⟨hEqualR, _⟩
    · exact depthsLexLT_asymm hDepthL hDepthR
    · exact depthsLexLT_not_equal hDepthL (fun r => (hEqualR r).symm)
  · rcases hRL with hDepthR | ⟨_, hTopR⟩
    · exact depthsLexLT_not_equal hDepthR (fun r => (hEqualL r).symm)
    · omega

/-- Exact strict comparison for the complete finite depth suffix and top value. -/
theorem keyLT_iff_of_common_chain (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p) :
    KeyLT (select F v) left right ↔ v left < v right := by
  constructor
  · intro hKey
    by_cases hlt : v left < v right
    · exact hlt
    · by_cases heq : v left = v right
      · exact False.elim (keyLT_not_keyEQ hKey (keyEQ_of_common_chain_value_eq F v hL hR hChain heq))
      · exact False.elim (keyLT_asymm hKey (keyLT_of_common_chain_value_lt F v hR hL
          (fun p => (hChain p).symm) (by omega)))
  · exact keyLT_of_common_chain_value_lt F v hL hR hChain

theorem keyEQ_iff_of_common_chain (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p) :
    KeyEQ (select F v) left right ↔ v left = v right := by
  constructor
  · intro hKey
    by_cases heq : v left = v right
    · exact heq
    · by_cases hlt : v left < v right
      · exact False.elim (keyLT_not_keyEQ (keyLT_of_common_chain_value_lt F v hL hR hChain hlt) hKey)
      · exact False.elim (keyLT_not_keyEQ (keyLT_of_common_chain_value_lt F v hR hL
          (fun p => (hChain p).symm) (by omega)) (keyEQ_symm hKey))
  · exact keyEQ_of_common_chain_value_eq F v hL hR hChain

def KeyLE (base : Row) (left right : Nat) : Prop :=
  KeyLT base left right ∨ KeyEQ base left right

theorem keyLE_iff_of_common_chain (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p) :
    KeyLE (select F v) left right ↔ v left ≤ v right := by
  rw [KeyLE, keyLT_iff_of_common_chain F v hL hR hChain,
    keyEQ_iff_of_common_chain F v hL hR hChain]
  omega

theorem keyLE_iff_of_common_parent (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hParent : F.parent left = F.parent right) :
    KeyLE (select F v) left right ↔ v left ≤ v right :=
  keyLE_iff_of_common_chain F v hL hR (ZeroY.Forest.ancestor_iff_of_parent_eq hParent)

theorem keyLE_next_iff_of_common_parent (base : Row) {left right : Nat}
    (hL : 0 < base.next.value left) (hR : 0 < base.next.value right)
    (hParent : base.forest.parent left = base.forest.parent right) :
    KeyLE base.next left right ↔ base.next.value left ≤ base.next.value right :=
  keyLE_iff_of_common_parent base.forest base.difference hL hR hParent

#print axioms height_next_of_parent
#print axioms keyLT_of_next
#print axioms keyLT_of_common_chain_value_lt
#print axioms keyEQ_of_common_chain_value_eq
#print axioms keyLT_iff_of_common_chain
#print axioms keyEQ_iff_of_common_chain
#print axioms keyLE_iff_of_common_chain
#print axioms height_eq_of_depthsEqual

end OneY.Numeric
