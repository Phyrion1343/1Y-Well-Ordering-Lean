import OneY.RootGeometry

/-!
# Computed reconstruction from a finite-height parent graph

The value function below is a genuine well-founded recursion on the column
index.  It does not assume the reconstruction equations as an input.  The
nearest-smaller/canonical property is intentionally outside this module.
-/

namespace OneY.Reconstruction

open RootGeometry

/-- Sum the contributions from all parents above the requested row. Every
recursive call uses a strictly smaller column. Nonexistent cells have value 0. -/
def value (M : RowMountain) (top : Nat → Nat) (r c : Nat) : Nat :=
  if r ≤ M.height c then
    top c + ((List.range' r (M.height c - r)).map fun u =>
      match _hp : (M.row u).parent c with
      | none => 0
      | some p => value M top u p).sum
  else 0
termination_by c
decreasing_by exact (M.row u).parent_left _hp

def parentValue (M : RowMountain) (top : Nat → Nat) (r c : Nat) : Nat :=
  match (M.row r).parent c with
  | none => 0
  | some p => value M top r p

theorem value_eq (M : RowMountain) (top : Nat → Nat) (r c : Nat) :
    value M top r c =
      if r ≤ M.height c then
        top c + ((List.range' r (M.height c-r)).map
          (fun u => parentValue M top u c)).sum
      else 0 := by
  rw [value]
  have hf : (fun u =>
      match _hp : (M.row u).parent c with
      | none => 0
      | some p => value M top u p) = (fun u => parentValue M top u c) := by
    funext u
    cases hp : (M.row u).parent c <;> simp [hp, parentValue]
  rw [hf]

theorem value_absent (M : RowMountain) (top : Nat → Nat) {r c : Nat}
    (h : M.height c < r) : value M top r c = 0 := by
  rw [value_eq]
  simp [Nat.not_le_of_gt h]

theorem value_top (M : RowMountain) (top : Nat → Nat) (c : Nat) :
    value M top (M.height c) c = top c := by
  rw [value_eq]
  simp

theorem top_le_value (M : RowMountain) (top : Nat → Nat) {r c : Nat}
    (h : r ≤ M.height c) : top c ≤ value M top r c := by
  rw [value_eq]
  simp only [h, ↓reduceIte]
  exact Nat.le_add_right _ _

theorem value_pos (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) {r c : Nat} (h : r ≤ M.height c) :
    0 < value M top r c :=
  Nat.lt_of_lt_of_le (hTop c) (top_le_value M top h)

theorem value_eq_succ_parentValue (M : RowMountain) (top : Nat → Nat)
    {r c : Nat} (h : r < M.height c) :
    value M top r c = value M top (r+1) c + parentValue M top r c := by
  rw [value_eq M top r c, value_eq M top (r+1) c]
  have hr : r ≤ M.height c := by omega
  have hr' : r+1 ≤ M.height c := by omega
  have hn : M.height c-r = (M.height c-(r+1))+1 := by omega
  simp only [hr, hr', ↓reduceIte]
  rw [hn, List.range'_succ, List.map_cons, List.sum_cons]
  omega

theorem value_recurrence (M : RowMountain) (top : Nat → Nat)
    {r c p : Nat} (hp : (M.row r).parent c = some p) :
    value M top r c = value M top (r+1) c + value M top r p := by
  rw [value_eq_succ_parentValue M top (M.parent_source hp)]
  simp [parentValue, hp]

theorem parent_value_lt (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) {r c p : Nat}
    (hp : (M.row r).parent c = some p) :
    value M top r p < value M top r c := by
  have hSource := M.parent_source hp
  have hPos := value_pos M top hTop (by omega : r+1 ≤ M.height c)
  rw [value_recurrence M top hp]
  omega

theorem next_row_value_lt (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) {r c : Nat} (h : r < M.height c) :
    value M top (r+1) c < value M top r c := by
  obtain ⟨p, hp⟩ := M.parent_exists r c h
  have hPos := value_pos M top hTop (M.parent_endpoint hp)
  rw [value_recurrence M top hp]
  omega

theorem value_pos_iff (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) (r c : Nat) :
    0 < value M top r c ↔ r ≤ M.height c := by
  constructor
  · intro hPos
    by_cases h : r ≤ M.height c
    · exact h
    · have hZero := value_absent M top (by omega : M.height c < r)
      omega
  · exact value_pos M top hTop

/-- The recurrence is a specification to be satisfied by a function, not
an assumption used to define `value`. -/
structure Reconstructs (M : RowMountain) (top : Nat → Nat)
    (v : Nat → Nat → Nat) : Prop where
  absent : ∀ r c, M.height c < r → v r c = 0
  top : ∀ c, v (M.height c) c = top c
  step : ∀ {r c p}, (M.row r).parent c = some p →
    v r c = v (r+1) c + v r p

theorem value_reconstructs (M : RowMountain) (top : Nat → Nat) :
    Reconstructs M top (value M top) where
  absent := fun _ _ h => value_absent M top h
  top := value_top M top
  step := value_recurrence M top

/-- First induct on the column. Inside a column, induct downward from its
finite top. Parents have already been uniquely reconstructed to the left. -/
theorem reconstructs_eq_value (M : RowMountain) (top : Nat → Nat)
    {v : Nat → Nat → Nat} (hv : Reconstructs M top v) : v = value M top := by
  have all : ∀ c r, v r c = value M top r c := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
        have below : ∀ gap r, r+gap = M.height c → v r c = value M top r c := by
          intro gap
          induction gap with
          | zero =>
              intro r hr
              have heq : r = M.height c := by omega
              rw [heq, hv.top c, value_top]
          | succ gap ihRow =>
              intro r hr
              have hRow : r < M.height c := by omega
              obtain ⟨p, hp⟩ := M.parent_exists r c hRow
              rw [hv.step hp, value_recurrence M top hp,
                ihRow (r+1) (by omega), ih p ((M.row r).parent_left hp) r]
        intro r
        by_cases hCell : r ≤ M.height c
        · exact below (M.height c-r) r (by omega)
        · have hAbsent : M.height c < r := by omega
          rw [hv.absent r c hAbsent, value_absent M top hAbsent]
  funext r c
  exact all c r

theorem reconstructs_unique (M : RowMountain) (top : Nat → Nat)
    {v w : Nat → Nat → Nat} (hv : Reconstructs M top v)
    (hw : Reconstructs M top w) : v = w :=
  (reconstructs_eq_value M top hv).trans (reconstructs_eq_value M top hw).symm

theorem exists_unique_reconstruction (M : RowMountain) (top : Nat → Nat) :
    ∃ v : Nat → Nat → Nat, Reconstructs M top v ∧
      ∀ w, Reconstructs M top w → w = v := by
  refine ⟨value M top, value_reconstructs M top, ?_⟩
  intro v hv
  exact reconstructs_eq_value M top hv

/-- Reconstruction of a prefix depends only on its own heights, parent
relations and top values. Columns strictly to its right are irrelevant. -/
theorem value_prefix_congr (M N : RowMountain) (topM topN : Nat → Nat)
    (n : Nat)
    (hHeight : ∀ c, c < n → M.height c = N.height c)
    (hParent : ∀ r c, c < n → (M.row r).parent c = (N.row r).parent c)
    (hTop : ∀ c, c < n → topM c = topN c) :
    ∀ c, c < n → ∀ r, value M topM r c = value N topN r c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro hc r
      rw [value_eq, value_eq, hHeight c hc, hTop c hc]
      by_cases hLive : r ≤ N.height c
      · simp only [hLive, ↓reduceIte]
        apply congrArg (fun a => topN c+a)
        apply congrArg List.sum
        apply List.map_congr_left
        intro u _
        unfold parentValue
        rw [hParent u c hc]
        cases hp : (N.row u).parent c with
        | none => rfl
        | some p =>
            simp only
            have hpc := (N.row u).parent_left hp
            exact ih p hpc (by omega) u
      · simp [hLive]

#print axioms value_reconstructs
#print axioms parent_value_lt
#print axioms reconstructs_unique
#print axioms exists_unique_reconstruction
#print axioms value_prefix_congr

end OneY.Reconstruction
