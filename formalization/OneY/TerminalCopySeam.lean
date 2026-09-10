import OneY.TerminalCopyCanonical

/-! # Nearest-smaller reconstruction at the first retained seam -/

namespace OneY.Numeric

theorem ancestor_transfer_le {F G : ParentForest} {a c : Nat}
    (hp : ∀ q, q ≤ c → F.parent q = G.parent q) (ha : F.Ancestor a c) :
    G.Ancestor a c :=
  ParentForest.ancestor_of_zeroY (ZeroY.Forest.ancestor_transfer_prefix F.parent_left
    (Nat.lt_succ_self c) (fun q hq => hp q (by omega)) (ParentForest.ancestor_to_zeroY ha))

theorem restrictedParent_of_target_lower (F G : ParentForest) (v w : Nat → Nat)
    {c p : Nat} (hp : restrictedParent F v c = some p)
    (hparent : ∀ q, q ≤ c → F.parent q = G.parent q)
    (hvalue : ∀ q, q < c → v q = w q)
    (hlower : v p < w c) (hupper : w c ≤ v c) :
    restrictedParent G w c = some p := by
  obtain ⟨ha, hpos, _, hmax⟩ := (restrictedParent_some_iff F v c p).mp hp
  have hpa := ParentForest.ancestor_of_zeroY ha
  have hplt := hpa.lt
  apply (restrictedParent_some_iff G w c p).mpr
  refine ⟨ParentForest.ancestor_to_zeroY (ancestor_transfer_le hparent hpa), ?_, ?_, ?_⟩
  · rw [← hvalue p hplt]
    exact hpos
  · rw [← hvalue p hplt]
    exact hlower
  · intro q hq hqpos hqval
    have hqa := ParentForest.ancestor_of_zeroY hq
    have hqlt := hqa.lt
    have hqold := ancestor_transfer_le (fun i hi => (hparent i hi).symm) hqa
    rw [← hvalue q hqlt] at hqpos hqval
    exact hmax q (ParentForest.ancestor_to_zeroY hqold) hqpos (by omega)

theorem restrictedParent_of_target_parent_value (F G : ParentForest) (v w : Nat → Nat)
    {c y : Nat} (hp : restrictedParent F v c = some y)
    (hparent : ∀ q, q ≤ c → F.parent q = G.parent q)
    (hvalue : ∀ q, q < c → v q = w q) (htarget : w c = v y) :
    restrictedParent G w c = restrictedParent F v y := by
  obtain ⟨hya0, _, hyv, hymax⟩ := (restrictedParent_some_iff F v c y).mp hp
  have hya := ParentForest.ancestor_of_zeroY hya0
  have hylt := hya.lt
  have lowerToY : ∀ q, G.Ancestor q c → 0 < w q → w q < w c →
      F.Ancestor q y ∧ 0 < v q ∧ v q < v y := by
    intro q hq hqpos hqval
    have hqlt := hq.lt
    have hqold := ancestor_transfer_le (fun i hi => (hparent i hi).symm) hq
    rw [← hvalue q hqlt] at hqpos hqval
    have hqy := hymax q (ParentForest.ancestor_to_zeroY hqold) hqpos (by omega)
    have hstrict : q < y := by
      by_cases he : q = y
      · subst q; omega
      · omega
    exact ⟨ParentForest.ancestor_of_zeroY (ZeroY.Forest.ancestor_of_common_target
      F.parent_left (ParentForest.ancestor_to_zeroY hqold) hya0 hstrict), hqpos, by omega⟩
  cases hn : restrictedParent F v y with
  | none =>
      apply (restrictedParent_none_iff G w c).mpr
      intro q hq hpos
      by_cases hlt : w q < w c
      · obtain ⟨ha, hpq, hvq⟩ := lowerToY q hq hpos hlt
        have h := (restrictedParent_none_iff F v y).mp hn q ha hpq
        omega
      · omega
  | some p =>
      obtain ⟨hpa0, hppos, hpv, hpmax⟩ := (restrictedParent_some_iff F v y p).mp hn
      have hpa := (ParentForest.ancestor_of_zeroY hpa0).trans hya
      have hplt := hpa.lt
      apply (restrictedParent_some_iff G w c p).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (ancestor_transfer_le hparent hpa), ?_, ?_, ?_⟩
      · rw [← hvalue p hplt]
        exact hppos
      · rw [← hvalue p hplt, htarget]
        exact hpv
      · intro q hq hqpos hqval
        obtain ⟨ha, hpq, hvq⟩ := lowerToY q (ParentForest.ancestor_of_zeroY hq) hqpos hqval
        exact hpmax q (ParentForest.ancestor_to_zeroY ha) hpq hvq

end OneY.Numeric

namespace OneY.TerminalCopy.Context

theorem parent_first_seam_below (C : Context) {r : Nat} (hr : r < C.level) :
    C.parent r C.coordinates.x = (C.mountain.row r).parent C.coordinates.x := by
  have h := C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr 0
  have hf : C.coordinates.parentCopy 0 = id := by
    funext p
    exact C.coordinates.parentCopy_zero p
  simpa only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero, hf, Option.map_id, id] using h

theorem parent_first_seam_above (C : Context) {r : Nat} (hr : C.level ≤ r) :
    C.parent r C.coordinates.x = (C.mountain.row r).parent C.coordinates.y := by
  have h := C.parent_root_copy_high hr 1
  simpa only [Nat.one_mul, C.coordinates.root_add_length] using h

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_restrictedParent_first_seam (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (r : Nat) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) x = (badAtTerminalContext a hbad).parent (r+1) x := by
  by_cases hhigh : d ≤ r
  · exact badAtTerminal_restrictedParent_above a hbad hhigh x
  · let C := badAtTerminalContext a hbad
    let v := (rows (layers a K).row (r+1)).value
    let w := Reconstruction.value C.toRowMountain
      (C.ordinaryContext.copyValue (topValue (layers a K).row)) (r+1)
    have hlow : r < C.level := by change r < d; omega
    have hparent : ∀ q, q ≤ x → (C.mountain.row r).parent q = (C.row r).parent q := by
      intro q hq
      by_cases hstrict : q < x
      · exact (C.parent_original hstrict r).symm
      · have he : q = x := by omega
        subst q
        exact (C.parent_first_seam_below hlow).symm
    have hvalue : ∀ q, q < x → v q = w q := by
      intro q hq
      have h := C.value_original (topValue (layers a K).row) hq (r+1)
      have hcell : Reconstruction.value C.mountain (topValue (layers a K).row) (r+1) q = v q :=
        Reconstruction.value_numeric_cell (layers a K).row (layers a K).positive (r+1) q
      exact (h.trans hcell).symm
    have hnext : r+1 ≤ d := by omega
    have htarget : w x+1 = v x := badAtTerminal_first_seam_succ a hbad hnext
    change restrictedParent (C.row r) w x = C.parent (r+1) x
    by_cases he : r+1 = d
    · have hold : restrictedParent (C.mountain.row r) v x = some y := by
        change (rows (layers a K).row (r+1)).forest.parent x = some y
        rw [he]
        exact hbad.1
      have hcrit : v x = v y+1 := by
        dsimp only [v]
        rw [he]
        exact hbad.2
      have h := restrictedParent_of_target_parent_value (C.mountain.row r) (C.row r)
        v w hold hparent hvalue (by omega)
      have hout := C.parent_first_seam_above (by change d ≤ r+1; omega : C.level ≤ r+1)
      change C.parent (r+1) x = (rows (layers a K).row (r+1)).forest.parent y at hout
      rw [hout]
      exact h
    · have hnextlow : r+1 < C.level := by change r+1 < d; omega
      have hh := C.last_height
      change height (layers a K).row x = d+1 at hh
      obtain ⟨p, hp⟩ := C.mountain.parent_exists (r+1) x (by change r+1 < height (layers a K).row x; omega)
      have hold : restrictedParent (C.mountain.row r) v x = some p := hp
      have hv := (rows (layers a K).row (r+1)).parent_values hp
      change 0 < v p ∧ v p < v x at hv
      have hnot : v x ≠ v p+1 := by
        intro hvone
        have hbad' : BadAt a K (r+1) x p := ⟨hp, hvone⟩
        have hu := badAt_unique hbad hbad'
        omega
      have h := restrictedParent_of_target_lower (C.mountain.row r) (C.row r)
        v w hold hparent hvalue (by omega) (by omega)
      have hout := C.parent_first_seam_below hnextlow
      change C.parent (r+1) x = (C.mountain.row (r+1)).parent x at hout
      rw [hout, hp]
      exact h

end OneY.Numeric

#print axioms OneY.Numeric.restrictedParent_of_target_parent_value
#print axioms OneY.Numeric.badAtTerminal_restrictedParent_first_seam
