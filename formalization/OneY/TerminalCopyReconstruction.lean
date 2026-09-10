import OneY.TerminalCopyNumeric
import OneY.OrdinaryCopyReconstruction

/-!
# Reconstruction at and above the active finite row

The active graph has the ordinary-copy heights. At and above the active
row its parent graph also agrees with ordinary copying, including the seam.
Consequently the actual reconstruction in all those rows is already fixed.
-/

namespace OneY.Reconstruction

theorem value_upper_congr (M N : RootGeometry.RowMountain) (top : Nat → Nat)
    (level : Nat) (hh : ∀ c, M.height c = N.height c)
    (hp : ∀ r, level ≤ r → ∀ c, (M.row r).parent c = (N.row r).parent c) :
    ∀ c r, level ≤ r → value M top r c = value N top r c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro r hr
      rw [value_eq M top r c, value_eq N top r c, hh c]
      by_cases hlive : r ≤ N.height c
      · simp only [hlive, ↓reduceIte]
        apply congrArg (fun a => top c+a)
        apply congrArg List.sum
        apply List.map_congr_left
        intro u hu
        have hu' := (List.mem_range'_1.mp hu).1
        have hlevel := Nat.le_trans hr hu'
        unfold parentValue
        rw [hp u hlevel c]
        cases hpu : (N.row u).parent c with
        | none => rfl
        | some p => exact ih p ((N.row u).parent_left hpu) u hlevel
      · simp only [hlive, ↓reduceIte]

end OneY.Reconstruction

namespace OneY.TerminalCopy.Context

def ordinaryContext (C : Context) : OrdinaryCopy.Context := ⟨C.mountain, C.coordinates⟩

theorem height_encode_eq_ordinary (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.height (C.coordinates.encode s b) = C.ordinaryContext.height (C.coordinates.encode s b) := by
  rw [C.height_encode hs hx b]
  by_cases he : s = C.coordinates.x
  · subst s
    rw [if_pos rfl]
    have h := C.ordinaryContext.height_parentCopy C.coordinates.root_lt_last (b+1)
    change C.ordinaryContext.height (C.coordinates.parentCopy (b+1) C.coordinates.y) =
      C.mountain.height C.coordinates.y at h
    rw [C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.root_copy_succ_eq] at h
    exact h.symm
  · rw [if_neg he]
    have hsx : s < C.coordinates.x := by omega
    have h := C.ordinaryContext.height_parentCopy hsx b
    change C.ordinaryContext.height (C.coordinates.parentCopy b s) = C.mountain.height s at h
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)] at h
    exact h.symm

theorem height_eq_ordinary (C : Context) (c : Nat) :
    C.height c = C.ordinaryContext.height c := by
  by_cases hold : c < C.coordinates.x
  · rw [C.height_original hold, C.ordinaryContext.height_original hold]
    rfl
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have hs := C.coordinates.source_bounds c
    have h := C.height_encode_eq_ordinary hs.1 hs.2 (C.coordinates.block c)
    rw [C.coordinates.encode_coordinates hc] at h
    exact h

theorem ordinary_parent_seam (C : Context) (b r : Nat) :
    C.ordinaryContext.parent r (C.coordinates.encode C.coordinates.x b) =
      (C.mountain.row r).parent C.coordinates.y := by
  have h := C.ordinaryContext.parent_parentCopy C.coordinates.root_lt_last (b+1) r
  change C.ordinaryContext.parent r (C.coordinates.parentCopy (b+1) C.coordinates.y) =
    ((C.mountain.row r).parent C.coordinates.y).map (C.coordinates.parentCopy (b+1)) at h
  rw [C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.root_copy_succ_eq] at h
  cases hp : (C.mountain.row r).parent C.coordinates.y with
  | none => simpa only [hp, Option.map_none, CopyCoordinates.Context.encode] using h
  | some p =>
      have hleft := (C.mountain.row r).parent_left hp
      simpa only [hp, Option.map_some, C.coordinates.parentCopy_good (b+1) hleft,
        CopyCoordinates.Context.encode] using h

theorem parent_encode_eq_ordinary_above (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hr : C.level ≤ r) (b : Nat) :
    C.parent r (C.coordinates.encode s b) =
      C.ordinaryContext.parent r (C.coordinates.encode s b) := by
  rw [C.parent_encode hs hx b r]
  by_cases he : s = C.coordinates.x
  · subst s
    rw [if_pos ⟨rfl, hr⟩, C.ordinary_parent_seam]
  · rw [if_neg (by intro h; exact he h.1)]
    have hsx : s < C.coordinates.x := by omega
    exact (C.ordinaryContext.parent_encode (Nat.le_of_lt hs) hsx b r).symm

theorem parent_eq_ordinary_above (C : Context) {r : Nat} (hr : C.level ≤ r) (c : Nat) :
    C.parent r c = C.ordinaryContext.parent r c := by
  by_cases hold : c < C.coordinates.x
  · rw [C.parent_original hold r, C.ordinaryContext.parent_original hold r]
    rfl
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have hs := C.coordinates.source_bounds c
    have h := C.parent_encode_eq_ordinary_above hs.1 hs.2 hr (C.coordinates.block c)
    rw [C.coordinates.encode_coordinates hc] at h
    exact h

theorem value_eq_ordinary_above (C : Context) (top : Nat → Nat) {r : Nat}
    (hr : C.level ≤ r) (c : Nat) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r c =
      Reconstruction.value C.ordinaryContext.toRowMountain (C.ordinaryContext.copyValue top) r c :=
  Reconstruction.value_upper_congr C.toRowMountain C.ordinaryContext.toRowMountain
    (C.ordinaryContext.copyValue top) C.level C.height_eq_ordinary
    (fun _ h q => C.parent_eq_ordinary_above h q) c r hr

theorem value_above (C : Context) (top : Nat → Nat) {r : Nat}
    (hr : C.level ≤ r) (c : Nat) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r c =
      Reconstruction.value C.mountain top r (C.ordinaryContext.source0 c) := by
  rw [C.value_eq_ordinary_above top hr, C.ordinaryContext.value_eq_source]
  rfl

theorem value_original (C : Context) (top : Nat → Nat) {c : Nat}
    (hc : c < C.coordinates.x) (r : Nat) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r c =
      Reconstruction.value C.mountain top r c :=
  Reconstruction.value_prefix_congr C.toRowMountain C.mountain
    (C.ordinaryContext.copyValue top) top C.coordinates.x
    (fun _ h => C.height_original h)
    (fun u _ h => C.parent_original h u)
    (fun _ h => C.ordinaryContext.copyValue_original top h) c hc r

theorem ordinary_source_first_seam (C : Context) :
    C.ordinaryContext.source0 C.coordinates.x = C.coordinates.y := by
  have h := C.ordinaryContext.source0_encode (Nat.le_refl C.coordinates.y)
    C.coordinates.root_lt_last 1
  change C.ordinaryContext.source0 (C.coordinates.encode C.coordinates.y 1) = C.coordinates.y at h
  simpa only [CopyCoordinates.Context.encode, Nat.one_mul, C.coordinates.root_add_length] using h

theorem value_first_seam_level (C : Context) (top : Nat → Nat) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top)
      C.level C.coordinates.x = Reconstruction.value C.mountain top C.level C.coordinates.y := by
  rw [C.value_above top (Nat.le_refl _), C.ordinary_source_first_seam]

/-- The critical difference of one propagates down the first seam because
all of its lower parent endpoints lie in the unchanged prefix. -/
theorem value_first_seam_succ (C : Context) (top : Nat → Nat)
    (hcrit : Reconstruction.value C.mountain top C.level C.coordinates.x =
      Reconstruction.value C.mountain top C.level C.coordinates.y+1)
    {r : Nat} (hr : r ≤ C.level) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r C.coordinates.x+1 =
      Reconstruction.value C.mountain top r C.coordinates.x := by
  have aux : ∀ gap r, r+gap = C.level →
      Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r C.coordinates.x+1 =
        Reconstruction.value C.mountain top r C.coordinates.x := by
    intro gap
    induction gap with
    | zero =>
        intro u hu
        have he : u = C.level := by omega
        rw [he, C.value_first_seam_level]
        exact hcrit.symm
    | succ gap ih =>
        intro u hu
        have hulow : u < C.level := by omega
        have hlast := C.last_height
        obtain ⟨p, hp⟩ := C.mountain.parent_exists u C.coordinates.x (by omega)
        have hleft := (C.mountain.row u).parent_left hp
        have hnew : (C.toRowMountain.row u).parent C.coordinates.x = some p := by
          have h := C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hulow 0
          rw [hp, Option.map_some, C.coordinates.parentCopy_zero] at h
          change C.parent u C.coordinates.x = some p
          simpa only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero] using h
        rw [Reconstruction.value_recurrence C.toRowMountain (C.ordinaryContext.copyValue top) hnew,
          Reconstruction.value_recurrence C.mountain top hp, C.value_original top hleft u]
        have hih := ih (u+1) (by omega)
        omega
  exact aux (C.level-r) r (by omega)

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_value_above (a : RootedRow) {K d x y r : Nat}
    (hbad : BadAt a K d x y) (hr : d ≤ r) (c : Nat) :
    Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) r c =
        (rows (layers a K).row r).value ((badAtTerminalContext a hbad).ordinaryContext.source0 c) := by
  rw [TerminalCopy.Context.value_above _ _ hr]
  exact Reconstruction.value_numeric_cell (layers a K).row (layers a K).positive r _

theorem badAtTerminal_first_seam_succ (a : RootedRow) {K d x y r : Nat}
    (hbad : BadAt a K d x y) (hr : r ≤ d) :
    Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) r x+1 =
        (rows (layers a K).row r).value x := by
  let C := badAtTerminalContext a hbad
  have hcrit : Reconstruction.value C.mountain (topValue (layers a K).row) C.level C.coordinates.x =
      Reconstruction.value C.mountain (topValue (layers a K).row) C.level C.coordinates.y+1 := by
    change Reconstruction.value (mountain (layers a K).row (layers a K).positive)
      (topValue (layers a K).row) d x =
        Reconstruction.value (mountain (layers a K).row (layers a K).positive)
          (topValue (layers a K).row) d y+1
    rw [Reconstruction.value_numeric_cell, Reconstruction.value_numeric_cell]
    exact hbad.2
  have h := C.value_first_seam_succ (topValue (layers a K).row) hcrit hr
  have hcell : Reconstruction.value C.mountain (topValue (layers a K).row) r C.coordinates.x =
      (rows (layers a K).row r).value x :=
    Reconstruction.value_numeric_cell (layers a K).row (layers a K).positive r x
  exact h.trans hcell

end OneY.Numeric

#print axioms OneY.Reconstruction.value_upper_congr
#print axioms OneY.TerminalCopy.Context.height_eq_ordinary
#print axioms OneY.TerminalCopy.Context.value_above
#print axioms OneY.Numeric.badAtTerminal_value_above
#print axioms OneY.Numeric.badAtTerminal_first_seam_succ
