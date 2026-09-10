import OneY.ReconstructionComparison
import OneY.Prefix

/-! # Finite-prefix versions of reconstructed key comparison -/

namespace OneY.ParentForest

theorem depth_prefix_congr (F G : ParentForest) (n : Nat)
    (h : ∀ c, c < n → F.parent c = G.parent c) :
    ∀ c, c < n → F.depth c = G.depth c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro hc
      cases hp : F.parent c with
      | none => rw [F.depth_of_parent_none hp, G.depth_of_parent_none ((h c hc).symm.trans hp)]
      | some p =>
          rw [F.depth_of_parent_some hp, G.depth_of_parent_some ((h c hc).symm.trans hp),
            ih p (F.parent_left hp) (by have := F.parent_left hp; omega)]

end OneY.ParentForest

namespace OneY.Reconstruction

open RootGeometry LowerCopy.Context

theorem numericRow_rows_agreesBelow (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u n : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ c, c < n →
      Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c)
    (k : Nat) : (Numeric.rows (numericRow M top hTop u) k).AgreesBelow
      (numericRow M top hTop (u+k)) n := by
  induction k with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ k ih =>
      have hn := ih.next
      have hd := numericRow_difference M top hTop (u+k)
      constructor
      · intro c hc
        have he := hn.1 c hc
        change _ = (numericRow M top hTop (u+k)).difference c at he
        rw [hd] at he
        exact he
      · intro c hc
        have he := hn.2 c hc
        change _ = Numeric.restrictedParent (M.row (u+k)) (numericRow M top hTop (u+k)).difference c at he
        rw [hd, hCanonical (u+k) (by omega) c hc] at he
        exact he

theorem topValue_of_rows_agree (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c)
    (a : Numeric.Row) (u n : Nat)
    (hAgree : ∀ k, (Numeric.rows a k).AgreesBelow (numericRow M top hTop (u+k)) n)
    {c : Nat} (hc : c < n) (hLive : u ≤ M.height c) : Numeric.topValue a c = top c := by
  have hPos : 0 < a.value c := by
    have hv := (hAgree 0).1 c hc
    change a.value c = value M top u c at hv
    rw [hv]
    exact value_pos M top hTop hLive
  have hAtTop := Numeric.height_live a hPos
  rw [(hAgree (Numeric.height a c)).1 c hc] at hAtTop
  have hLe : u+Numeric.height a c ≤ M.height c := (value_pos_iff M top hTop _ _).mp hAtTop
  have hOldLive : 0 < (Numeric.rows a (M.height c-u)).value c := by
    rw [(hAgree (M.height c-u)).1 c hc]
    change 0 < value M top (u+(M.height c-u)) c
    have he : u+(M.height c-u) = M.height c := by omega
    rw [he, value_top]
    exact hTop c
  have hGe := (Numeric.live_iff_le_height a hPos _).mp hOldLive
  have he : u+Numeric.height a c = M.height c := by omega
  unfold Numeric.topValue
  rw [(hAgree (Numeric.height a c)).1 c hc]
  change value M top (u+Numeric.height a c) c = top c
  rw [he, value_top]

theorem keyLEFrom_iff_numericKey_of_agrees (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c)
    (a : Numeric.Row) (u n : Nat)
    (hAgree : ∀ k, (Numeric.rows a k).AgreesBelow (numericRow M top hTop (u+k)) n)
    {c z : Nat} (hc : c < n) (hz : z < n) (hcLive : u ≤ M.height c) (hzLive : u ≤ M.height z) :
    KeyLEFrom M top u c z ↔ Numeric.KeyLE a c z := by
  have hDepth : ∀ k q, q < n → (Numeric.rows a k).forest.depth q = (M.row (u+k)).depth q := by
    intro k q hq
    exact ParentForest.depth_prefix_congr _ _ n (hAgree k).2 q hq
  have hEq : DepthsEqualFrom M u c z ↔ Numeric.DepthsEqual a c z := by
    constructor
    · intro h k
      rw [hDepth k c hc, hDepth k z hz]
      exact h _ (by omega)
    · intro h r hr
      have ht := h (r-u)
      rw [hDepth (r-u) c hc, hDepth (r-u) z hz] at ht
      have he : u+(r-u) = r := by omega
      rwa [he] at ht
  have hLT : DepthsLTFrom M u c z ↔ Numeric.DepthsLexLT a c z := by
    constructor
    · rintro ⟨r, hr, hBefore, hDiff⟩
      refine ⟨r-u, ?_, ?_⟩
      · intro k hk
        rw [hDepth k c hc, hDepth k z hz]
        exact hBefore _ (by omega) (by omega)
      · rw [hDepth (r-u) c hc, hDepth (r-u) z hz]
        have he : u+(r-u) = r := by omega
        rwa [he]
    · rintro ⟨k, hBefore, hDiff⟩
      refine ⟨u+k, by omega, ?_, ?_⟩
      · intro r hr hrk
        have ht := hBefore (r-u) (by omega)
        rw [hDepth (r-u) c hc, hDepth (r-u) z hz] at ht
        have he : u+(r-u) = r := by omega
        rwa [he] at ht
      · rwa [hDepth k c hc, hDepth k z hz] at hDiff
  rw [KeyLEFrom, hLT, hEq, Numeric.KeyLE, Numeric.KeyLT, Numeric.KeyEQ,
    topValue_of_rows_agree M top hTop a u n hAgree hc hcLive,
    topValue_of_rows_agree M top hTop a u n hAgree hz hzLive]
  constructor
  · rintro (h | ⟨hEq, hTop⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.eq_or_lt_of_le hTop with he | hl
      · exact Or.inr ⟨hEq, he⟩
      · exact Or.inl (Or.inr ⟨hEq, hl⟩)
  · rintro ((h | ⟨hEq, hTop⟩) | ⟨hEq, hTop⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hEq, Nat.le_of_lt hTop⟩
    · exact Or.inr ⟨hEq, Nat.le_of_eq hTop⟩

theorem keyLEFrom_iff_value_le_prefix (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u n : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ i, i < n →
      Numeric.restrictedParent (M.row r) (value M top (r+1)) i = (M.row (r+1)).parent i)
    {c z : Nat} (hc : c < n) (hz : z < n) (hcLive : u < M.height c) (hzLive : u < M.height z)
    (hParent : (M.row u).parent c = (M.row u).parent z) :
    KeyLEFrom M top (u+1) c z ↔ value M top (u+1) c ≤ value M top (u+1) z := by
  have hAgree : ∀ k, (Numeric.rows (numericRow M top hTop u).next k).AgreesBelow
      (numericRow M top hTop (u+1+k)) n := by
    intro k
    rw [Numeric.rows_next]
    have he : u+1+k = u+(k+1) := by omega
    rw [he]
    exact numericRow_rows_agreesBelow M top hTop u n hCanonical (k+1)
  rw [keyLEFrom_iff_numericKey_of_agrees M top hTop (numericRow M top hTop u).next (u+1) n
    hAgree hc hz (by omega) (by omega)]
  have hDiff := numericRow_difference M top hTop u
  have hL : 0 < (numericRow M top hTop u).next.value c := by
    change 0 < (numericRow M top hTop u).difference c
    rw [hDiff]
    exact value_pos M top hTop (by omega)
  have hR : 0 < (numericRow M top hTop u).next.value z := by
    change 0 < (numericRow M top hTop u).difference z
    rw [hDiff]
    exact value_pos M top hTop (by omega)
  have ht := Numeric.keyLE_next_iff_of_common_parent (numericRow M top hTop u) hL hR hParent
  change _ ↔ (numericRow M top hTop u).difference c ≤ (numericRow M top hTop u).difference z at ht
  rwa [hDiff] at ht

#print axioms numericRow_rows_agreesBelow
#print axioms keyLEFrom_iff_value_le_prefix

end OneY.Reconstruction
