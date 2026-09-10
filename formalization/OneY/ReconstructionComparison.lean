import OneY.LowerCopyComparison

/-! # Comparison of reconstructed values using already restored higher rows

Only higher-row NS equations are assumed. The row whose parent is currently
being restored need not be canonical.
-/

namespace OneY.Reconstruction

open RootGeometry LowerCopy.Context

def numericRow (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (r : Nat) : Numeric.Row where
  value := value M top r
  forest := M.row r
  parent_values hp := ⟨value_pos M top hTop (M.parent_endpoint hp), parent_value_lt M top hTop hp⟩

theorem numericRow_difference (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (r : Nat) :
    (numericRow M top hTop r).difference = value M top (r+1) := by
  funext c
  cases hp : (M.row r).parent c with
  | none =>
      have hh := (M.parent_none_iff r c).mp hp
      rw [Numeric.Row.difference]
      change (match (M.row r).parent c with | none => 0 | some p => value M top r c-value M top r p) = _
      simp only [hp]
      exact (value_absent M top (by omega : M.height c < r+1)).symm
  | some p =>
      rw [Numeric.Row.difference]
      change (match (M.row r).parent c with | none => 0 | some p => value M top r c-value M top r p) = _
      simp only [hp]
      rw [value_recurrence M top hp, Nat.add_sub_cancel]

theorem numericRow_next (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) {r : Nat}
    (hNS : ∀ c, Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c) :
    (numericRow M top hTop r).next = numericRow M top hTop (r+1) := by
  have hForest : (Numeric.select (M.row r) (value M top (r+1))).forest = M.row (r+1) :=
    Numeric.parentForest_eq_of_parent_eq _ _ hNS
  change Numeric.select (M.row r) (numericRow M top hTop r).difference = _
  rw [numericRow_difference]
  cases hA : Numeric.select (M.row r) (value M top (r+1)) with
  | mk v F hp =>
      have hv : v = value M top (r+1) := by
        have ht := congrArg Numeric.Row.value hA
        exact ht.symm
      have hf : F = M.row (r+1) := by rw [← hForest, hA]
      subst v
      subst F
      rfl

theorem numericRow_rows (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ c,
      Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c)
    (k : Nat) : Numeric.rows (numericRow M top hTop u) k = numericRow M top hTop (u+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (Numeric.rows (numericRow M top hTop u) k).next = _
      rw [ih, numericRow_next M top hTop (hCanonical (u+k) (by omega))]
      rfl

theorem numericRow_topValue (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ c,
      Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c)
    {c : Nat} (hc : u ≤ M.height c) : Numeric.topValue (numericRow M top hTop u) c = top c := by
  let a := numericRow M top hTop u
  have hPos : 0 < a.value c := value_pos M top hTop hc
  have hLive := Numeric.height_live a hPos
  change 0 < (Numeric.rows (numericRow M top hTop u) (Numeric.height a c)).value c at hLive
  rw [numericRow_rows M top hTop u hCanonical] at hLive
  have hLe : u+Numeric.height a c ≤ M.height c := (value_pos_iff M top hTop _ _).mp hLive
  have hOldLive : 0 < (Numeric.rows a (M.height c-u)).value c := by
    change 0 < (Numeric.rows (numericRow M top hTop u) (M.height c-u)).value c
    rw [numericRow_rows M top hTop u hCanonical]
    change 0 < value M top (u+(M.height c-u)) c
    have he : u+(M.height c-u) = M.height c := by omega
    rw [he, value_top]
    exact hTop c
  have hGe := (Numeric.live_iff_le_height a hPos _).mp hOldLive
  have he : u+Numeric.height a c = M.height c := by omega
  unfold Numeric.topValue
  change (Numeric.rows (numericRow M top hTop u) (Numeric.height a c)).value c = top c
  rw [numericRow_rows M top hTop u hCanonical]
  change value M top (u+Numeric.height a c) c = top c
  rw [he, value_top]

theorem keyLEFrom_iff_numericKey (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ c,
      Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c)
    {c z : Nat} (hc : u ≤ M.height c) (hz : u ≤ M.height z) :
    KeyLEFrom M top u c z ↔ Numeric.KeyLE (numericRow M top hTop u) c z := by
  have hDepth : ∀ k q, (Numeric.rows (numericRow M top hTop u) k).forest.depth q = (M.row (u+k)).depth q := by
    intro k q
    rw [numericRow_rows M top hTop u hCanonical]
    rfl
  have hEq : DepthsEqualFrom M u c z ↔ Numeric.DepthsEqual (numericRow M top hTop u) c z := by
    constructor
    · intro h k
      rw [hDepth, hDepth]
      exact h _ (by omega)
    · intro h r hr
      have ht := h (r-u)
      rw [hDepth, hDepth] at ht
      have he : u+(r-u) = r := by omega
      rwa [he] at ht
  have hLT : DepthsLTFrom M u c z ↔ Numeric.DepthsLexLT (numericRow M top hTop u) c z := by
    constructor
    · rintro ⟨r, hr, hBefore, hDiff⟩
      refine ⟨r-u, ?_, ?_⟩
      · intro k hk
        rw [hDepth, hDepth]
        exact hBefore _ (by omega) (by omega)
      · rw [hDepth, hDepth]
        have he : u+(r-u) = r := by omega
        rwa [he]
    · rintro ⟨k, hBefore, hDiff⟩
      refine ⟨u+k, by omega, ?_, ?_⟩
      · intro r hr hrk
        have ht := hBefore (r-u) (by omega)
        rw [hDepth, hDepth] at ht
        have he : u+(r-u) = r := by omega
        rwa [he] at ht
      · rwa [hDepth, hDepth] at hDiff
  rw [KeyLEFrom, hLT, hEq, Numeric.KeyLE, Numeric.KeyLT, Numeric.KeyEQ,
    numericRow_topValue M top hTop u hCanonical hc,
    numericRow_topValue M top hTop u hCanonical hz]
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

/-- Shared parents compare their next-row values using only higher-row
canonicality; the shared-parent row itself is not assumed canonical. -/
theorem keyLEFrom_iff_value_le (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (u : Nat)
    (hCanonical : ∀ r, u ≤ r → ∀ c,
      Numeric.restrictedParent (M.row r) (value M top (r+1)) c = (M.row (r+1)).parent c)
    {c z : Nat} (hc : u < M.height c) (hz : u < M.height z)
    (hParent : (M.row u).parent c = (M.row u).parent z) :
    KeyLEFrom M top (u+1) c z ↔ value M top (u+1) c ≤ value M top (u+1) z := by
  rw [keyLEFrom_iff_numericKey M top hTop (u+1) (fun r hr => hCanonical r (by omega)) (by omega) (by omega),
    ← numericRow_next M top hTop (hCanonical u (Nat.le_refl _))]
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

#print axioms numericRow_rows
#print axioms numericRow_topValue
#print axioms keyLEFrom_iff_value_le

end OneY.Reconstruction
