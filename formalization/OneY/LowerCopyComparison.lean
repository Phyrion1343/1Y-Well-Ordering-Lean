import OneY.LowerCopyDepths
import OneY.SparseDepth
import OneY.TopComparison
import ZeroY.Forest.AncestorMonotone

/-! # Depth comparison transport for the computed lower copy -/

namespace OneY.ParentForest

theorem parent_eq_of_common_chain_depth_eq (F G : ParentForest)
    (hNS : ∀ c, ZeroY.Forest.nearestSmaller F.parent G.depth c = G.parent c)
    {c z : Nat}
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent c p ↔ ZeroY.Forest.Ancestor F.parent z p)
    (hDepth : G.depth c = G.depth z) : G.parent c = G.parent z := by
  cases hp : G.parent c with
  | none =>
      have hNone := (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mp
        ((hNS c).trans hp)
      have hz : G.parent z = none := by
        rw [← hNS z]
        apply (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mpr
        intro p ha
        rw [← hDepth]
        exact hNone p ((hChain p).mpr ha)
      exact hz.symm
  | some p =>
      obtain ⟨ha, hv, hm⟩ := (ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mp
        ((hNS c).trans hp)
      have hz : G.parent z = some p := by
        rw [← hNS z]
        apply (ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mpr
        refine ⟨(hChain p).mp ha, by omega, ?_⟩
        intro q hq hqv
        exact hm q ((hChain q).mpr hq) (by omega)
      exact hz.symm

/-- Monotonicity concerns the ancestor indicator, not just scalar depth. -/
theorem ancestor_mono_of_common_chain_depth (F G : ParentForest)
    (hNS : ∀ c, ZeroY.Forest.nearestSmaller F.parent G.depth c = G.parent c)
    {c z a : Nat}
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent c p ↔ ZeroY.Forest.Ancestor F.parent z p)
    (hDepth : G.depth c ≤ G.depth z) (ha : G.Ancestor a c) : G.Ancestor a z := by
  have hMap : ZeroY.Forest.nearestSmaller F.parent G.depth = G.parent := funext hNS
  have hOld := ancestor_to_zeroY ha
  rw [← hMap] at hOld
  have hNew := ZeroY.Forest.nearestSmaller_ancestor_mono F.parent_left hChain hDepth hOld
  rw [hMap] at hNew
  exact ancestor_of_zeroY hNew

end OneY.ParentForest

namespace OneY.Numeric

theorem Row.next_ancestor_mono_of_common_parent_depth (a : Row) {c z p : Nat}
    (hParent : a.forest.parent c = a.forest.parent z)
    (hDepth : a.next.forest.depth c ≤ a.next.forest.depth z)
    (ha : a.next.forest.Ancestor p c) : a.next.forest.Ancestor p z :=
  ParentForest.ancestor_mono_of_common_chain_depth a.forest a.next.forest
    a.next_depth_nearestSmaller (ZeroY.Forest.ancestor_iff_of_parent_eq hParent) hDepth ha

end OneY.Numeric

namespace OneY.LowerCopy.Context

/-- This is a proved property of old numerical mountains (see below), not a
requirement on the copied numerical reconstruction. -/
def DepthRegular (C : Context) : Prop :=
  ∀ r c, ZeroY.Forest.nearestSmaller (C.mountain.row r).parent
    (C.mountain.row (r+1)).depth c = (C.mountain.row (r+1)).parent c

theorem depthRegular_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase) :
    C.DepthRegular := by
  intro r c
  rw [hMountain]
  exact (Numeric.rows base r).next_depth_nearestSmaller c

theorem parent_eq_of_previous_depth_eq (C : Context) (hRegular : C.DepthRegular)
    {r c z : Nat} (hPrevious : (C.mountain.row r).parent c = (C.mountain.row r).parent z)
    (hDepth : (C.mountain.row (r+1)).depth c = (C.mountain.row (r+1)).depth z) :
    (C.mountain.row (r+1)).parent c = (C.mountain.row (r+1)).parent z :=
  ParentForest.parent_eq_of_common_chain_depth_eq _ _ (hRegular r)
    (ZeroY.Forest.ancestor_iff_of_parent_eq hPrevious) hDepth

theorem parent_eq_of_depths_before (C : Context) (hRegular : C.DepthRegular)
    {u r c z : Nat} (hur : u ≤ r)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : ∀ i, u < i → i ≤ r → (C.mountain.row i).depth c = (C.mountain.row i).depth z) :
    (C.mountain.row r).parent c = (C.mountain.row r).parent z := by
  induction r with
  | zero =>
      have he : u = 0 := by omega
      subst u
      exact hInitial
  | succ r ih =>
      by_cases he : u = r+1
      · subst u; exact hInitial
      · apply C.parent_eq_of_previous_depth_eq hRegular
          (ih (by omega) (fun i hi hj => hDepth i hi (by omega)))
        exact hDepth (r+1) (by omega) (Nat.le_refl _)

theorem ancestor_mono_of_previous_depth (C : Context) (hRegular : C.DepthRegular)
    {u c z a : Nat} (hPrevious : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : (C.mountain.row (u+1)).depth c ≤ (C.mountain.row (u+1)).depth z)
    (ha : (C.mountain.row (u+1)).Ancestor a c) : (C.mountain.row (u+1)).Ancestor a z :=
  ParentForest.ancestor_mono_of_common_chain_depth _ _ (hRegular u)
    (ZeroY.Forest.ancestor_iff_of_parent_eq hPrevious) hDepth ha

theorem depth_low_lt_of_previous (C : Context) (hRegular : C.DepthRegular)
    {u c z : Nat} (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hPrevious : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : (C.mountain.row (u+1)).depth c < (C.mountain.row (u+1)).depth z)
    (hr : u+1 < C.floor) (b : Nat) :
    (C.row (u+1)).depth (C.coordinates.parentCopy b c) <
      (C.row (u+1)).depth (C.coordinates.parentCopy b z) := by
  by_cases hAncC : (C.mountain.row (u+1)).Ancestor C.coordinates.y c
  · have hAncZ := C.ancestor_mono_of_previous_depth hRegular hPrevious (Nat.le_of_lt hDepth) hAncC
    rw [C.depth_low_of_root_ancestor hcx (Or.inr hAncC) hr b,
      C.depth_low_of_root_ancestor hzx (Or.inr hAncZ) hr b]
    omega
  · rw [C.depth_low_of_no_root_ancestor hcx (by omega) hAncC hr b]
    by_cases hAncZ : (C.mountain.row (u+1)).Ancestor C.coordinates.y z
    · rw [C.depth_low_of_root_ancestor hzx (Or.inr hAncZ) hr b]
      omega
    · rw [C.depth_low_of_no_root_ancestor hzx (by omega) hAncZ hr b]
      exact hDepth

theorem depth_low_eq_of_previous (C : Context) (hRegular : C.DepthRegular)
    {u c z : Nat} (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hPrevious : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : (C.mountain.row (u+1)).depth c = (C.mountain.row (u+1)).depth z)
    (hr : u+1 < C.floor) (b : Nat) :
    (C.row (u+1)).depth (C.coordinates.parentCopy b c) =
      (C.row (u+1)).depth (C.coordinates.parentCopy b z) := by
  by_cases hAncC : (C.mountain.row (u+1)).Ancestor C.coordinates.y c
  · have hAncZ := C.ancestor_mono_of_previous_depth hRegular hPrevious (Nat.le_of_eq hDepth) hAncC
    rw [C.depth_low_of_root_ancestor hcx (Or.inr hAncC) hr b,
      C.depth_low_of_root_ancestor hzx (Or.inr hAncZ) hr b, hDepth]
  · have hAncZ : ¬ (C.mountain.row (u+1)).Ancestor C.coordinates.y z := by
      intro ha
      exact hAncC (C.ancestor_mono_of_previous_depth hRegular hPrevious.symm
        (Nat.le_of_eq hDepth.symm) ha)
    rw [C.depth_low_of_no_root_ancestor hcx (by omega) hAncC hr b,
      C.depth_low_of_no_root_ancestor hzx (by omega) hAncZ hr b, hDepth]

theorem inCone_iff_root_ancestor (C : Context) {s : Nat} (hs : s ≠ C.coordinates.y) :
    C.InCone s ↔ (C.mountain.row C.floor).Ancestor C.coordinates.y s := by
  constructor
  · intro hCone
    rcases (C.mountain.rootAt_eq_iff_path (r := C.floor)
      (q := C.coordinates.y) (c := s) rfl).mp hCone.2 with ha | he
    · exact ha
    · exact False.elim (hs he.symm)
  · intro ha
    have hLive : C.floor ≤ C.mountain.height s := by
      cases ha with
      | direct hp => exact Nat.le_of_lt (C.mountain.parent_source hp)
      | step _ hp => exact Nat.le_of_lt (C.mountain.parent_source hp)
    exact ⟨hLive, (C.mountain.rootAt_eq_iff_path (r := C.floor)
      (q := C.coordinates.y) (c := s) rfl).mpr (Or.inl ha)⟩

theorem inCone_eq_of_floor_depth_eq (C : Context) (hRegular : C.DepthRegular)
    {u c z : Nat} (hc : c ≠ C.coordinates.y) (hz : z ≠ C.coordinates.y)
    (hFloor : C.floor = u+1)
    (hPrevious : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : (C.mountain.row C.floor).depth c = (C.mountain.row C.floor).depth z) :
    C.InCone c ↔ C.InCone z := by
  rw [C.inCone_iff_root_ancestor hc, C.inCone_iff_root_ancestor hz, hFloor] at *
  exact ⟨C.ancestor_mono_of_previous_depth hRegular hPrevious (Nat.le_of_eq hDepth),
    C.ancestor_mono_of_previous_depth hRegular hPrevious.symm (Nat.le_of_eq hDepth.symm)⟩

theorem depth_floor_lt_of_previous (C : Context) (hRegular : C.DepthRegular)
    {u c z : Nat} (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hFloor : C.floor = u+1)
    (hPrevious : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hDepth : (C.mountain.row C.floor).depth c < (C.mountain.row C.floor).depth z) (b : Nat) :
    (C.row C.floor).depth (C.coordinates.parentCopy b c) <
      (C.row C.floor).depth (C.coordinates.parentCopy b z) := by
  by_cases hConeC : C.InCone c
  · have hConeZ : C.InCone z := by
      rw [C.inCone_iff_root_ancestor (by omega)]
      have ha := (C.inCone_iff_root_ancestor (by omega : c ≠ C.coordinates.y)).mp hConeC
      rw [hFloor] at ha ⊢
      apply C.ancestor_mono_of_previous_depth hRegular hPrevious ?_ ha
      simpa only [← hFloor] using Nat.le_of_lt hDepth
    rw [C.depth_floor_inCone hc hcx hConeC b, C.depth_floor_inCone hz hzx hConeZ b]
    omega
  · rw [C.depth_outside_high hcx hConeC (Nat.le_refl _) b]
    by_cases hConeZ : C.InCone z
    · rw [C.depth_floor_inCone hz hzx hConeZ b]
      omega
    · rw [C.depth_outside_high hzx hConeZ (Nat.le_refl _) b]
      exact hDepth

theorem depth_low_eq_of_initial (C : Context) (hRegular : C.DepthRegular)
    {u r c z : Nat} (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hur : u < r) (hr : r < C.floor)
    (hBefore : ∀ i, u < i → i ≤ r → (C.mountain.row i).depth c = (C.mountain.row i).depth z)
    (b : Nat) : (C.row r).depth (C.coordinates.parentCopy b c) =
      (C.row r).depth (C.coordinates.parentCopy b z) := by
  cases r with
  | zero => omega
  | succ r =>
      exact C.depth_low_eq_of_previous hRegular hc hcx hz hzx
        (C.parent_eq_of_depths_before hRegular (by omega) hInitial
          (fun i hi hj => hBefore i hi (by omega)))
        (hBefore (r+1) (by omega) (Nat.le_refl _)) hr b

def DepthsEqualFrom (M : RootGeometry.RowMountain) (u c z : Nat) : Prop :=
  ∀ r, u ≤ r → (M.row r).depth c = (M.row r).depth z

def DepthsLTFrom (M : RootGeometry.RowMountain) (u c z : Nat) : Prop :=
  ∃ r, u ≤ r ∧ (∀ i, u ≤ i → i < r → (M.row i).depth c = (M.row i).depth z) ∧
    (M.row r).depth c < (M.row r).depth z

/-- Copying a synchronized contour preserves every depth suffix coordinate. -/
theorem depthsEqual_lifted (C : Context) {u c z : Nat}
    (hcx : c ≤ C.coordinates.x) (hzx : z ≤ C.coordinates.x)
    (hConeC : C.InCone c) (hConeZ : C.InCone z) (hu : C.floor ≤ u)
    (hEqual : DepthsEqualFrom C.mountain u c z) (b : Nat) :
    DepthsEqualFrom C.toRowMountain (u+b*C.rise)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  intro r hr
  have hStart : u ≤ r-b*C.rise := by omega
  have he : r-b*C.rise+b*C.rise = r := by omega
  change (C.row r).depth _ = (C.row r).depth _
  rw [← he, C.depth_lifted hcx hConeC (by omega) b,
    C.depth_lifted hzx hConeZ (by omega) b]
  exact hEqual _ hStart

theorem depthsLT_lifted (C : Context) {u c z : Nat}
    (hcx : c ≤ C.coordinates.x) (hzx : z ≤ C.coordinates.x)
    (hConeC : C.InCone c) (hConeZ : C.InCone z) (hu : C.floor ≤ u)
    (hLess : DepthsLTFrom C.mountain u c z) (b : Nat) :
    DepthsLTFrom C.toRowMountain (u+b*C.rise)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  obtain ⟨r, hr, hBefore, hDiff⟩ := hLess
  refine ⟨r+b*C.rise, by omega, ?_, ?_⟩
  · intro i hi hir
    have he : i-b*C.rise+b*C.rise = i := by omega
    change (C.row i).depth _ = (C.row i).depth _
    rw [← he, C.depth_lifted hcx hConeC (by omega) b,
      C.depth_lifted hzx hConeZ (by omega) b]
    exact hBefore _ (by omega) (by omega)
  · change (C.row (r+b*C.rise)).depth _ < (C.row (r+b*C.rise)).depth _
    rw [C.depth_lifted hcx hConeC (by omega) b, C.depth_lifted hzx hConeZ (by omega) b]
    exact hDiff

theorem depthsEqual_from_floor (C : Context) {c z : Nat}
    (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hCone : C.InCone c ↔ C.InCone z)
    (hEqual : DepthsEqualFrom C.mountain C.floor c z) (b : Nat) :
    DepthsEqualFrom C.toRowMountain C.floor
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  intro r hr
  change (C.row r).depth _ = (C.row r).depth _
  by_cases hConeC : C.InCone c
  · have hConeZ := hCone.mp hConeC
    by_cases hFill : r < C.floor+b*C.rise
    · rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hc),
        C.coordinates.parentCopy_bad b (Nat.le_of_lt hz)]
      change (C.row r).depth (C.coordinates.encode c b) =
        (C.row r).depth (C.coordinates.encode z b)
      rw [C.depth_fill hc hcx hConeC b hr hFill,
        C.depth_fill hz hzx hConeZ b hr hFill, hEqual C.floor (Nat.le_refl _)]
    · exact C.depthsEqual_lifted hcx hzx hConeC hConeZ (Nat.le_refl _) hEqual b r (by omega)
  · have hConeZ : ¬ C.InCone z := fun h => hConeC (hCone.mpr h)
    rw [C.depth_outside_high hcx hConeC hr b, C.depth_outside_high hzx hConeZ hr b]
    exact hEqual r hr

/-- When the first difference is above the reference floor, equal earlier
coordinates make the inserted reference word identical on both columns. -/
theorem depthsLT_after_floor (C : Context) {c z r : Nat}
    (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hCone : C.InCone c ↔ C.InCone z) (hr : C.floor < r)
    (hBefore : ∀ i, C.floor ≤ i → i < r →
      (C.mountain.row i).depth c = (C.mountain.row i).depth z)
    (hDiff : (C.mountain.row r).depth c < (C.mountain.row r).depth z) (b : Nat) :
    DepthsLTFrom C.toRowMountain C.floor
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  by_cases hConeC : C.InCone c
  · have hConeZ := hCone.mp hConeC
    refine ⟨r+b*C.rise, by omega, ?_, ?_⟩
    · intro i hi hir
      change (C.row i).depth _ = (C.row i).depth _
      by_cases hFill : i < C.floor+b*C.rise
      · rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hc),
          C.coordinates.parentCopy_bad b (Nat.le_of_lt hz)]
        change (C.row i).depth (C.coordinates.encode c b) = (C.row i).depth (C.coordinates.encode z b)
        rw [C.depth_fill hc hcx hConeC b hi hFill,
          C.depth_fill hz hzx hConeZ b hi hFill, hBefore C.floor (Nat.le_refl _) hr]
      · have he : i-b*C.rise+b*C.rise = i := by omega
        rw [← he, C.depth_lifted hcx hConeC (by omega) b,
          C.depth_lifted hzx hConeZ (by omega) b]
        exact hBefore _ (by omega) (by omega)
    · change (C.row (r+b*C.rise)).depth _ < (C.row (r+b*C.rise)).depth _
      rw [C.depth_lifted hcx hConeC (by omega) b, C.depth_lifted hzx hConeZ (by omega) b]
      exact hDiff
  · have hConeZ : ¬ C.InCone z := fun h => hConeC (hCone.mpr h)
    refine ⟨r, by omega, ?_, ?_⟩
    · intro i hi hir
      change (C.row i).depth _ = (C.row i).depth _
      rw [C.depth_outside_high hcx hConeC hi b, C.depth_outside_high hzx hConeZ hi b]
      exact hBefore i hi hir
    · change (C.row r).depth _ < (C.row r).depth _
      rw [C.depth_outside_high hcx hConeC (by omega) b,
        C.depth_outside_high hzx hConeZ (by omega) b]
      exact hDiff

theorem depthsEqual_low_start (C : Context) (hRegular : C.DepthRegular) {u c z : Nat}
    (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hu : u < C.floor)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hEqual : DepthsEqualFrom C.mountain (u+1) c z) (b : Nat) :
    DepthsEqualFrom C.toRowMountain (u+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have hFloor : C.floor = (C.floor-1)+1 := by omega
  have hCone := C.inCone_eq_of_floor_depth_eq hRegular (by omega) (by omega) hFloor
    (C.parent_eq_of_depths_before hRegular (by omega) hInitial
      (fun i hi _ => hEqual i (by omega))) (hEqual _ (by omega))
  intro r hr
  by_cases hLow : r < C.floor
  · exact C.depth_low_eq_of_initial hRegular hc hcx hz hzx hInitial (by omega) hLow
      (fun i hi _ => hEqual i (by omega)) b
  · exact C.depthsEqual_from_floor hc hcx hz hzx hCone
      (fun i hi => hEqual i (by omega)) b r (by omega)

theorem depthsLT_low_start (C : Context) (hRegular : C.DepthRegular) {u c z : Nat}
    (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hu : u < C.floor)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hLess : DepthsLTFrom C.mountain (u+1) c z) (b : Nat) :
    DepthsLTFrom C.toRowMountain (u+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  obtain ⟨r, hr, hBefore, hDiff⟩ := hLess
  have hLowBefore : ∀ i, u+1 ≤ i → i < r → i < C.floor →
      (C.row i).depth (C.coordinates.parentCopy b c) = (C.row i).depth (C.coordinates.parentCopy b z) := by
    intro i hi hir hLow
    exact C.depth_low_eq_of_initial hRegular hc hcx hz hzx hInitial (by omega) hLow
      (fun j hj hji => hBefore j (by omega) (by omega)) b
  by_cases hrLow : r < C.floor
  · refine ⟨r, hr, fun i hi hir => hLowBefore i hi hir (by omega), ?_⟩
    cases r with
    | zero => omega
    | succ r =>
        exact C.depth_low_lt_of_previous hRegular hc hcx hz hzx
          (C.parent_eq_of_depths_before hRegular (by omega) hInitial
            (fun i hi hj => hBefore i (by omega) (by omega))) hDiff hrLow b
  · by_cases hrEq : r = C.floor
    · subst r
      refine ⟨C.floor, hr, fun i hi hir => hLowBefore i hi hir hir, ?_⟩
      have hFloor : C.floor = (C.floor-1)+1 := by omega
      exact C.depth_floor_lt_of_previous hRegular hc hcx hz hzx hFloor
        (C.parent_eq_of_depths_before hRegular (by omega) hInitial
          (fun i hi hj => hBefore i (by omega) (by omega))) hDiff b
    · have hFloor : C.floor = (C.floor-1)+1 := by omega
      have hCone := C.inCone_eq_of_floor_depth_eq hRegular (by omega) (by omega) hFloor
        (C.parent_eq_of_depths_before hRegular (by omega) hInitial
          (fun i hi hj => hBefore i (by omega) (by omega))) (hBefore _ (by omega) (by omega))
      obtain ⟨t, ht, htBefore, htDiff⟩ := C.depthsLT_after_floor hc hcx hz hzx hCone (by omega)
        (fun i hi hir => hBefore i (by omega) hir) hDiff b
      refine ⟨t, by omega, ?_, htDiff⟩
      intro i hi hit
      by_cases hLow : i < C.floor
      · exact hLowBefore i hi (by omega) hLow
      · exact htBefore i (by omega) hit

theorem height_eq_of_depthsEqualFrom (C : Context) {u c z : Nat}
    (hc : u < C.mountain.height c) (hz : u < C.mountain.height z)
    (hEqual : DepthsEqualFrom C.mountain (u+1) c z) :
    C.mountain.height c = C.mountain.height z := by
  have hCZero := (C.mountain.row (C.mountain.height c)).depth_of_parent_none
    ((C.mountain.parent_none_iff _ _).mpr (Nat.le_refl _))
  have hZZero := (C.mountain.row (C.mountain.height z)).depth_of_parent_none
    ((C.mountain.parent_none_iff _ _).mpr (Nat.le_refl _))
  have hCZ : (C.mountain.row (C.mountain.height c)).parent z = none :=
    ((C.mountain.row _).depth_zero_iff z).mp ((hEqual _ (by omega)).symm.trans hCZero)
  have hZC : (C.mountain.row (C.mountain.height z)).parent c = none :=
    ((C.mountain.row _).depth_zero_iff c).mp ((hEqual _ (by omega)).trans hZZero)
  have hLe := (C.mountain.parent_none_iff _ _).mp hCZ
  have hGe := (C.mountain.parent_none_iff _ _).mp hZC
  omega

theorem pseudo_eq_of_height_parent_eq (C : Context) {c z : Nat}
    (hHeight : C.mountain.height c = C.mountain.height z)
    (hParent : (C.mountain.row (C.mountain.height c-1)).parent c =
      (C.mountain.row (C.mountain.height z-1)).parent z) :
    Pseudo.parent C.mountain c = Pseudo.parent C.mountain z := by
  have hChain : ∀ p, Pseudo.Candidate C.mountain c p ↔ Pseudo.Candidate C.mountain z p := by
    intro p
    unfold Pseudo.Candidate
    rw [← hHeight]
    rw [← hHeight] at hParent
    exact and_congr (by
      rw [ParentForest.ancestor_iff_zeroY, ParentForest.ancestor_iff_zeroY]
      exact ZeroY.Forest.ancestor_iff_of_parent_eq hParent p) Iff.rfl
  cases hp : Pseudo.parent C.mountain c with
  | none =>
      have hNone := (Pseudo.parent_none_iff C.mountain c).mp hp
      exact ((Pseudo.parent_none_iff C.mountain z).mpr (hHeight.symm.trans hNone)).symm
  | some p =>
      obtain ⟨hPos, hCand, hMax⟩ := (Pseudo.parent_some_iff C.mountain c p).mp hp
      exact ((Pseudo.parent_some_iff C.mountain z p).mpr
        ⟨by omega, (hChain p).mp hCand, fun q hq => hMax q ((hChain q).mpr hq)⟩).symm

theorem pseudo_eq_of_depthsEqualFrom (C : Context) (hRegular : C.DepthRegular) {u c z : Nat}
    (hc : u < C.mountain.height c) (hz : u < C.mountain.height z)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hEqual : DepthsEqualFrom C.mountain (u+1) c z) :
    Pseudo.parent C.mountain c = Pseudo.parent C.mountain z := by
  have hHeight := C.height_eq_of_depthsEqualFrom hc hz hEqual
  apply C.pseudo_eq_of_height_parent_eq hHeight
  rw [← hHeight]
  exact C.parent_eq_of_depths_before hRegular (by omega) hInitial
    (fun i hi _ => hEqual i (by omega))

/-- Exactly the upper-layer B input, restricted to its shared pseudo-parent
window. It does not assert lower numerical comparison or canonicality. -/
def UpperOrder (C : Context) (oldTop newTop : Nat → Nat) : Prop :=
  ∀ z c, C.coordinates.y < z → z < c → c ≤ C.coordinates.x →
    Pseudo.parent C.mountain c = Pseudo.parent C.mountain z →
    oldTop c ≤ oldTop z → ∀ b,
    newTop (C.coordinates.parentCopy b c) ≤ newTop (C.coordinates.parentCopy b z)

def KeyLEFrom (M : RootGeometry.RowMountain) (top : Nat → Nat) (u c z : Nat) : Prop :=
  DepthsLTFrom M u c z ∨ (DepthsEqualFrom M u c z ∧ top c ≤ top z)

theorem keyLE_low_start (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {u c z : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hcLive : u < C.mountain.height c) (hzLive : u < C.mountain.height z)
    (hu : u < C.floor)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hKey : KeyLEFrom C.mountain oldTop (u+1) c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop (u+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  rcases hKey with hLess | ⟨hEqual, hTop⟩
  · exact Or.inl (C.depthsLT_low_start hRegular (by omega) hcx hz (by omega) hu hInitial hLess b)
  · exact Or.inr ⟨C.depthsEqual_low_start hRegular (by omega) hcx hz (by omega) hu hInitial hEqual b,
      hUpper z c hz hzc hcx
        (C.pseudo_eq_of_depthsEqualFrom hRegular hcLive hzLive hInitial hEqual) hTop b⟩

theorem depth_eq_of_same_parent (F : ParentForest) {c z : Nat} (hp : F.parent c = F.parent z) :
    F.depth c = F.depth z := by
  cases hc : F.parent c with
  | none => rw [F.depth_of_parent_none hc, F.depth_of_parent_none (hp.symm.trans hc)]
  | some p => rw [F.depth_of_parent_some hc, F.depth_of_parent_some (hp.symm.trans hc)]

theorem inCone_iff_of_same_floor_parent (C : Context) {c z : Nat}
    (hc : c ≠ C.coordinates.y) (hz : z ≠ C.coordinates.y)
    (hParent : (C.mountain.row C.floor).parent c = (C.mountain.row C.floor).parent z) :
    C.InCone c ↔ C.InCone z := by
  rw [C.inCone_iff_root_ancestor hc, C.inCone_iff_root_ancestor hz,
    ParentForest.ancestor_iff_zeroY, ParentForest.ancestor_iff_zeroY]
  exact ZeroY.Forest.ancestor_iff_of_parent_eq hParent _

theorem depth_floor_eq_of_same_parent (C : Context) {c z : Nat}
    (hc : C.coordinates.y < c) (hcx : c ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hParent : (C.mountain.row C.floor).parent c = (C.mountain.row C.floor).parent z) (b : Nat) :
    (C.row C.floor).depth (C.coordinates.parentCopy b c) =
      (C.row C.floor).depth (C.coordinates.parentCopy b z) := by
  have hDepth := depth_eq_of_same_parent _ hParent
  have hCone := C.inCone_iff_of_same_floor_parent (by omega) (by omega) hParent
  by_cases hConeC : C.InCone c
  · rw [C.depth_floor_inCone hc hcx hConeC b, C.depth_floor_inCone hz hzx (hCone.mp hConeC) b, hDepth]
  · have hConeZ : ¬ C.InCone z := fun h => hConeC (hCone.mpr h)
    rw [C.depth_outside_high hcx hConeC (Nat.le_refl _) b,
      C.depth_outside_high hzx hConeZ (Nat.le_refl _) b, hDepth]

theorem keyLE_floor_start (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {c z : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hcLive : C.floor < C.mountain.height c) (hzLive : C.floor < C.mountain.height z)
    (hInitial : (C.mountain.row C.floor).parent c = (C.mountain.row C.floor).parent z)
    (hKey : KeyLEFrom C.mountain oldTop (C.floor+1) c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop (C.floor+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have hDepth := depth_eq_of_same_parent _ hInitial
  have hCone := C.inCone_iff_of_same_floor_parent (by omega) (by omega) hInitial
  rcases hKey with ⟨r, hr, hBefore, hDiff⟩ | ⟨hEqual, hTop⟩
  · have hAllBefore : ∀ i, C.floor ≤ i → i < r →
        (C.mountain.row i).depth c = (C.mountain.row i).depth z := by
      intro i hi hir
      by_cases he : i = C.floor
      · subst i; exact hDepth
      · exact hBefore i (by omega) hir
    obtain ⟨t, ht, htBefore, htDiff⟩ := C.depthsLT_after_floor (by omega) hcx hz (by omega)
      hCone (by omega) hAllBefore hDiff b
    have htStrict : C.floor < t := by
      have heq := C.depth_floor_eq_of_same_parent (by omega) hcx hz (by omega) hInitial b
      change (C.row t).depth _ < (C.row t).depth _ at htDiff
      by_cases he : t = C.floor
      · rw [he, heq] at htDiff; omega
      · omega
    exact Or.inl ⟨t, by omega, fun i hi hit => htBefore i (by omega) hit, htDiff⟩
  · have hAllEqual : DepthsEqualFrom C.mountain C.floor c z := by
      intro i hi
      by_cases he : i = C.floor
      · subst i; exact hDepth
      · exact hEqual i (by omega)
    refine Or.inr ⟨?_, hUpper z c hz hzc hcx
      (C.pseudo_eq_of_depthsEqualFrom hRegular hcLive hzLive hInitial hEqual) hTop b⟩
    intro i hi
    exact C.depthsEqual_from_floor (by omega) hcx hz (by omega) hCone hAllEqual b i (by omega)

theorem keyLE_lifted_start (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {u c z : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hcLive : u < C.mountain.height c) (hzLive : u < C.mountain.height z)
    (hu : C.floor ≤ u) (hConeC : C.InCone c) (hConeZ : C.InCone z)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hKey : KeyLEFrom C.mountain oldTop (u+1) c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop (u+b*C.rise+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have he : u+b*C.rise+1 = u+1+b*C.rise := by omega
  rw [he]
  rcases hKey with hLess | ⟨hEqual, hTop⟩
  · exact Or.inl (C.depthsLT_lifted hcx (by omega) hConeC hConeZ (by omega) hLess b)
  · exact Or.inr ⟨C.depthsEqual_lifted hcx (by omega) hConeC hConeZ (by omega) hEqual b,
      hUpper z c hz hzc hcx
        (C.pseudo_eq_of_depthsEqualFrom hRegular hcLive hzLive hInitial hEqual) hTop b⟩

theorem keyLE_outside_start (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {u c z : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hcLive : u < C.mountain.height c) (hzLive : u < C.mountain.height z)
    (hu : C.floor ≤ u) (hOutC : ¬ C.InCone c) (hOutZ : ¬ C.InCone z)
    (hInitial : (C.mountain.row u).parent c = (C.mountain.row u).parent z)
    (hKey : KeyLEFrom C.mountain oldTop (u+1) c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop (u+1)
      (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have hDepth : ∀ r, u+1 ≤ r → ∀ s, s = c ∨ s = z →
      (C.row r).depth (C.coordinates.parentCopy b s) = (C.mountain.row r).depth s := by
    intro r hr s hs
    rcases hs with he | he <;> subst s
    · exact C.depth_outside_high hcx hOutC (by omega) b
    · exact C.depth_outside_high (by omega) hOutZ (by omega) b
  rcases hKey with ⟨r, hr, hBefore, hDiff⟩ | ⟨hEqual, hTop⟩
  · refine Or.inl ⟨r, hr, ?_, ?_⟩
    · intro i hi hir
      change (C.row i).depth _ = (C.row i).depth _
      rw [hDepth i hi c (Or.inl rfl), hDepth i hi z (Or.inr rfl)]
      exact hBefore i hi hir
    · change (C.row r).depth _ < (C.row r).depth _
      rw [hDepth r hr c (Or.inl rfl), hDepth r hr z (Or.inr rfl)]
      exact hDiff
  · refine Or.inr ⟨?_, hUpper z c hz hzc hcx
      (C.pseudo_eq_of_depthsEqualFrom hRegular hcLive hzLive hInitial hEqual) hTop b⟩
    intro r hr
    change (C.row r).depth _ = (C.row r).depth _
    rw [hDepth r hr c (Or.inl rfl), hDepth r hr z (Or.inr rfl)]
    exact hEqual r hr

#print axioms depthRegular_numeric
#print axioms ancestor_mono_of_previous_depth
#print axioms depth_low_lt_of_previous
#print axioms depth_low_eq_of_previous
#print axioms depthsEqual_low_start
#print axioms depthsLT_low_start
#print axioms pseudo_eq_of_depthsEqualFrom
#print axioms keyLE_low_start
#print axioms keyLE_floor_start
#print axioms keyLE_lifted_start
#print axioms keyLE_outside_start

end OneY.LowerCopy.Context
