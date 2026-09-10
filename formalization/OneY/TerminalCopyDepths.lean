import OneY.TerminalCopyExternal

/-! # Computed low-row depths in every terminal copied block -/

namespace OneY.TerminalCopy.Context

theorem parent_low_original (C : Context) {r c : Nat} (hr : r < C.level)
    (hc : c ≤ C.coordinates.x) : C.parent r c = (C.mountain.row r).parent c := by
  by_cases hlt : c < C.coordinates.x
  · exact C.parent_original hlt r
  · have he : c = C.coordinates.x := by omega
    subst c
    have ht := C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr 0
    have hid : C.coordinates.parentCopy 0 = id := funext C.coordinates.parentCopy_zero
    simpa only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero, hid, Option.map_id, id] using ht

theorem parent_low_parentCopy (C : Context) {r s : Nat} (hr : r < C.level)
    (hs : s ≤ C.coordinates.x) (hNot : s ≠ C.coordinates.y) (b : Nat) :
    C.parent r (C.coordinates.parentCopy b s) = ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  by_cases hx : s < C.coordinates.x
  · exact C.parent_parentCopy_nonroot hx hNot b r
  · have he : s = C.coordinates.x := by omega
    subst s
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last)]
    exact C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr b

theorem depth_original_low (C : Context) {r c : Nat} (hr : r < C.level)
    (hc : c ≤ C.coordinates.x) : (C.row r).depth c = (C.mountain.row r).depth c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : (C.mountain.row r).parent c with
      | none =>
          have hn : (C.row r).parent c = none := (C.parent_low_original hr hc).trans hp
          rw [(C.row r).depth_of_parent_none hn, (C.mountain.row r).depth_of_parent_none hp]
      | some p =>
          have hn : (C.row r).parent c = some p := (C.parent_low_original hr hc).trans hp
          rw [(C.row r).depth_of_parent_some hn, (C.mountain.row r).depth_of_parent_some hp,
            ih p ((C.mountain.row r).parent_left hp) (by have := (C.mountain.row r).parent_left hp; omega)]

theorem depth_low_ancestor (C : Context) {a c r : Nat}
    (hc : c ≤ C.coordinates.x) (haRoot : C.coordinates.y ≤ a)
    (ha : (C.mountain.row r).Ancestor a c) (b : Nat) (hr : r < C.level) :
    (C.row r).depth (c+b*C.coordinates.length)+(C.mountain.row r).depth a =
      (C.row r).depth (a+b*C.coordinates.length)+(C.mountain.row r).depth c := by
  induction ha with
  | @direct c hp =>
      have hpLeft := (C.mountain.row r).parent_left hp
      have hNew : C.parent r (c+b*C.coordinates.length) = some (a+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
          C.coordinates.parentCopy_bad b haRoot]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp]
      omega
  | @step p c ha hp ih =>
      have hpLeft := (C.mountain.row r).parent_left hp
      have haLeft := ha.lt
      have hPrev := ih (by omega)
      have hNew : C.parent r (c+b*C.coordinates.length) = some (p+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
          C.coordinates.parentCopy_bad b (by omega)]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp]
      omega

theorem depth_root_low (C : Context) {r : Nat} (hr : r < C.level) (b : Nat) :
    (C.row r).depth (C.coordinates.y+b*C.coordinates.length) =
      (C.mountain.row r).depth C.coordinates.y+
        b*((C.mountain.row r).depth C.coordinates.x-(C.mountain.row r).depth C.coordinates.y) := by
  have hPath := C.root_ancestor_last (Nat.le_of_lt hr)
  have hDepth := hPath.depth_lt
  induction b with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero] using C.depth_original_low hr (Nat.le_of_lt C.coordinates.root_lt_last)
  | succ b ih =>
      rw [C.root_copy_succ_eq]
      have he := C.depth_low_ancestor (Nat.le_refl _) (Nat.le_refl _) hPath b hr
      rw [ih] at he
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem depth_low_of_root_ancestor (C : Context) {s r : Nat}
    (hs : s ≤ C.coordinates.x)
    (hPath : C.coordinates.y = s ∨ (C.mountain.row r).Ancestor C.coordinates.y s)
    (hr : r < C.level) (b : Nat) :
    (C.row r).depth (C.coordinates.parentCopy b s) = (C.mountain.row r).depth s+
      b*((C.mountain.row r).depth C.coordinates.x-(C.mountain.row r).depth C.coordinates.y) := by
  rcases hPath with he | ha
  · subst s
    rw [C.coordinates.parentCopy_bad b (Nat.le_refl _)]
    exact C.depth_root_low hr b
  · have hLeft := ha.lt
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hLeft)]
    have ht := C.depth_low_ancestor hs (Nat.le_refl _) ha b hr
    rw [C.depth_root_low hr b] at ht
    omega

theorem depth_low_of_no_root_ancestor (C : Context) {s r : Nat}
    (hs : s ≤ C.coordinates.x) (hne : s ≠ C.coordinates.y)
    (hNo : ¬ (C.mountain.row r).Ancestor C.coordinates.y s)
    (hr : r < C.level) (b : Nat) :
    (C.row r).depth (C.coordinates.parentCopy b s) = (C.mountain.row r).depth s := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
      cases hp : (C.mountain.row r).parent s with
      | none =>
          have hn : (C.row r).parent (C.coordinates.parentCopy b s) = none := by
            change C.parent r _ = _
            rw [C.parent_low_parentCopy hr hs hne b, hp, Option.map_none]
          rw [(C.row r).depth_of_parent_none hn, (C.mountain.row r).depth_of_parent_none hp]
      | some p =>
          have hpLeft := (C.mountain.row r).parent_left hp
          have hpNe : p ≠ C.coordinates.y := by
            intro he
            subst p
            exact hNo (ParentForest.Ancestor.direct hp)
          have hpNo : ¬ (C.mountain.row r).Ancestor C.coordinates.y p := by
            intro ha
            exact hNo (ParentForest.Ancestor.step ha hp)
          have hn : (C.row r).parent (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
            change C.parent r _ = _
            rw [C.parent_low_parentCopy hr hs hne b, hp, Option.map_some]
          rw [(C.row r).depth_of_parent_some hn, (C.mountain.row r).depth_of_parent_some hp,
            ih p hpLeft (by omega) hpNe hpNo]

end OneY.TerminalCopy.Context

#print axioms OneY.TerminalCopy.Context.depth_low_of_root_ancestor
#print axioms OneY.TerminalCopy.Context.depth_low_of_no_root_ancestor
