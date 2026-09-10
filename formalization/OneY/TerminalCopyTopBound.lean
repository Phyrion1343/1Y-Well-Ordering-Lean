import OneY.TerminalFrameParents
import OneY.ReconstructionTop
import OneY.OrdinaryCopyExtraction

/-! # Positive lower bounds survive the terminal seam

The deleted last column is a descendant of the bad root in every active
higher parent row. Its strict-record property makes each inserted seam
preserve lower bounds along candidate paths. No new numeric selection is
assumed here.
-/

namespace OneY.ParentForest

def PositiveBound (F : ParentForest) (v : Nat → Nat) (bound c : Nat) : Prop :=
  ∀ q, q = c ∨ F.Ancestor q c → 0 < v q → bound ≤ v q

theorem PositiveBound.of_ancestor {F : ParentForest} {v : Nat → Nat} {bound a c : Nat}
    (h : F.PositiveBound v bound c) (ha : F.Ancestor a c) : F.PositiveBound v bound a := by
  intro q hq hpos
  apply h q (Or.inr ?_) hpos
  rcases hq with rfl | hq
  · exact ha
  · exact hq.trans ha

end OneY.ParentForest

namespace OneY.TerminalCopy.Context

theorem positiveBound_parent_preimage (C : Context) (v : Nat → Nat) {r bound s b p : Nat}
    (hr : r < C.level)
    (hSplice : (C.mountain.row r).PositiveBound v bound C.coordinates.y →
      (C.mountain.row r).PositiveBound v bound C.coordinates.x)
    (hs : s < C.coordinates.x) (hSafe : (C.mountain.row r).PositiveBound v bound s)
    (hp : C.parent r (C.coordinates.parentCopy b s) = some p) :
    ∃ q j, q < C.coordinates.x ∧ (C.mountain.row r).PositiveBound v bound q ∧
      p = C.coordinates.parentCopy j q := by
  by_cases hroot : s = C.coordinates.y
  · subst s
    cases b with
    | zero =>
        rw [C.coordinates.parentCopy_zero, C.parent_original C.coordinates.root_lt_last r] at hp
        have hlt := (C.mountain.row r).parent_left hp
        refine ⟨p, 0, by have := C.coordinates.root_lt_last; omega,
          hSafe.of_ancestor (ParentForest.Ancestor.direct hp), ?_⟩
        exact (C.coordinates.parentCopy_zero p).symm
    | succ b =>
        rw [C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.root_copy_succ_eq] at hp
        change C.parent r (C.coordinates.encode C.coordinates.x b) = some p at hp
        rw [C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr b] at hp
        obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp hp
        exact ⟨q, b, (C.mountain.row r).parent_left hq,
          (hSplice hSafe).of_ancestor (ParentForest.Ancestor.direct hq), he.symm⟩
  · rw [C.parent_parentCopy_nonroot hs hroot b r] at hp
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp hp
    have hlt := (C.mountain.row r).parent_left hq
    exact ⟨q, b, by omega, hSafe.of_ancestor (ParentForest.Ancestor.direct hq), he.symm⟩

theorem positiveBound_copy (C : Context) (v : Nat → Nat) {r bound : Nat}
    (hr : r < C.level)
    (hSplice : (C.mountain.row r).PositiveBound v bound C.coordinates.y →
      (C.mountain.row r).PositiveBound v bound C.coordinates.x)
    {s : Nat} (hs : s < C.coordinates.x)
    (hSafe : (C.mountain.row r).PositiveBound v bound s) (b : Nat) :
    (C.row r).PositiveBound (C.ordinaryContext.copyValue v) bound (C.coordinates.parentCopy b s) := by
  have main : ∀ n s b, C.coordinates.parentCopy b s = n → s < C.coordinates.x →
      (C.mountain.row r).PositiveBound v bound s →
      (C.row r).PositiveBound (C.ordinaryContext.copyValue v) bound n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro s b he hs hSafe q hq hpos
        rcases hq with hself | ha
        · subst q
          have hv : C.ordinaryContext.copyValue v (C.coordinates.parentCopy b s) = v s :=
            C.ordinaryContext.copyValue_parentCopy v hs b
          rw [← he, hv] at hpos ⊢
          exact hSafe s (Or.inl rfl) hpos
        · cases ha with
          | direct hp =>
              have hp' : C.parent r (C.coordinates.parentCopy b s) = some q := by rw [he]; exact hp
              obtain ⟨t, j, ht, hSafeT, hq⟩ := C.positiveBound_parent_preimage v hr hSplice hs hSafe hp'
              have hv : C.ordinaryContext.copyValue v (C.coordinates.parentCopy j t) = v t :=
                C.ordinaryContext.copyValue_parentCopy v ht j
              rw [hq, hv] at hpos ⊢
              exact hSafeT t (Or.inl rfl) hpos
          | @step p n ha hp =>
              have hp' : C.parent r (C.coordinates.parentCopy b s) = some p := by rw [he]; exact hp
              obtain ⟨t, j, ht, hSafeT, hpEq⟩ := C.positiveBound_parent_preimage v hr hSplice hs hSafe hp'
              exact ih p ((C.row r).parent_left hp) t j hpEq.symm ht hSafeT q (Or.inr ha) hpos
  exact main _ s b rfl hs hSafe

theorem positiveBound_copy_high (C : Context) (v : Nat → Nat) {r bound s : Nat}
    (hr : C.level ≤ r) (hs : s < C.coordinates.x)
    (hSafe : (C.mountain.row r).PositiveBound v bound s) (b : Nat) :
    (C.row r).PositiveBound (C.ordinaryContext.copyValue v) bound (C.coordinates.parentCopy b s) := by
  have hRows : C.row r = C.ordinaryContext.row r := by
    apply ParentForest.ext_parent
    funext q
    exact C.parent_eq_ordinary_above hr q
  rw [hRows]
  intro q hq hpos
  rcases hq with he | ha
  · have hv : C.ordinaryContext.copyValue v (C.coordinates.parentCopy b s) = v s :=
      C.ordinaryContext.copyValue_parentCopy v hs b
    rw [he, hv] at hpos ⊢
    exact hSafe s (Or.inl rfl) hpos
  · obtain ⟨p, hp, he⟩ := (C.ordinaryContext.ancestor_parentCopy_iff hs b).mp ha
    have hlt := hp.lt
    have hpBound : p < C.coordinates.x := by omega
    rw [he, C.ordinaryContext.copyValue_parentCopy v hpBound b] at hpos ⊢
    exact hSafe p (Or.inr hp) hpos

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem select_ancestor_record (F : ParentForest) (v : Nat → Nat) {a c : Nat}
    (ha : (select F v).forest.Ancestor a c) :
    0 < v a ∧ v a < v c ∧
      ∀ q, F.Ancestor q c → a < q → 0 < v q → v a < v q := by
  have hPos : 0 < v a := by
    induction ha with
    | direct hp => exact ((select F v).parent_values hp).1
    | step _ _ ih => exact ih
  have hCPos : 0 < v c := by
    cases ha with
    | direct hp =>
        have h := (select F v).parent_values hp
        change 0 < v a ∧ v a < v c at h
        omega
    | @step p c _ hp =>
        have h := (select F v).parent_values hp
        change 0 < v p ∧ v p < v c at h
        omega
  obtain ⟨cap, hcap⟩ := exists_value_cap v (c+1)
  have hDense := ancestor_to_filled_of_prefix (select F v) F hcap
    (fun _ _ => rfl) (Nat.lt_succ_self c) ha
  have hRec := ZeroY.Forest.nearestSmaller_ancestor_record F.parent_left
    (ParentForest.ancestor_to_zeroY hDense)
  change filledValue cap v a < filledValue cap v c ∧
    (∀ q, ZeroY.Forest.Ancestor F.parent c q → a < q →
      filledValue cap v a < filledValue cap v q) at hRec
  refine ⟨hPos, ?_, ?_⟩
  · simpa only [filledValue_positive cap v hPos, filledValue_positive cap v hCPos] using hRec.1
  · intro q hq hlt hqPos
    simpa only [filledValue_positive cap v hPos, filledValue_positive cap v hqPos] using
      hRec.2 q (ParentForest.ancestor_to_zeroY hq) hlt

theorem positiveBound_splice (F : ParentForest) (v : Nat → Nat) {a c bound : Nat}
    (ha : (select F v).forest.Ancestor a c)
    (hSafe : F.PositiveBound v bound a) : F.PositiveBound v bound c := by
  have hRec := select_ancestor_record F v ha
  have hBound := hSafe a (Or.inl rfl) hRec.1
  have hAnc := ParentForest.Refines.ancestor (select_refines F v) ha
  intro q hq hpos
  rcases hq with rfl | hq
  · omega
  · by_cases hlt : a < q
    · have hv := hRec.2.2 q hq hlt hpos
      omega
    · by_cases he : q = a
      · rw [he]; exact hBound
      · have hqa : F.Ancestor q a := ParentForest.ancestor_of_zeroY
          (ZeroY.Forest.ancestor_of_common_target F.parent_left
            (ParentForest.ancestor_to_zeroY hq) (ParentForest.ancestor_to_zeroY hAnc) (by omega))
        exact hSafe q (Or.inr hqa) hpos

theorem top_positiveBound (base : Row) (hpos : ∀ q, 0 < base.value q)
    {c r : Nat} (hHeight : height base c = r+1) :
    (rows base r).forest.PositiveBound (rows base (r+1)).value (topValue base c) c := by
  have hnone := top_parent_none base (hpos c)
  rw [hHeight] at hnone
  have hnone' : restrictedParent (rows base r).forest (rows base (r+1)).value c = none := hnone
  have ht : (rows base (r+1)).value c = topValue base c := by
    unfold topValue
    rw [hHeight]
  intro q hq hqpos
  rcases hq with rfl | hq
  · rw [ht]; exact Nat.le_refl _
  · rw [← ht]
    exact (restrictedParent_none_iff _ _ _).mp hnone' q hq hqpos

theorem badAtTerminal_pseudoTopBound (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    Reconstruction.PseudoTopBound (badAtTerminalContext a hbad).toRowMountain
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) := by
  let C := badAtTerminalContext a hbad
  let base := (layers a K).row
  let M := C.toRowMountain
  intro c p hp hHeights
  let r := M.height c-1
  let s := C.ordinaryContext.source0 c
  let b := C.ordinaryContext.block0 c
  have hs : s < C.coordinates.x := C.ordinaryContext.source0_bounds c
  have hCoord : C.coordinates.parentCopy b s = c := C.ordinaryContext.parentCopy_coordinates c
  have hPositive : 0 < M.height c := ((Pseudo.parent_some_iff M c p).mp hp).1
  have hRow : M.height c = r+1 := by dsimp [r]; omega
  have hHeight (q : Nat) : height base (C.ordinaryContext.source0 q) = M.height q := by
    have ht := C.height_parentCopy (C.ordinaryContext.source0_bounds q) (C.ordinaryContext.block0 q)
    have he : C.coordinates.parentCopy (C.ordinaryContext.block0 q)
        (C.ordinaryContext.source0 q) = q := C.ordinaryContext.parentCopy_coordinates q
    rw [he] at ht
    exact ht.symm
  have hSourceHeight : height base s = r+1 := (hHeight c).trans hRow
  let v := (rows base (r+1)).value
  have hSafe : (C.mountain.row r).PositiveBound v (topValue base s) s :=
    top_positiveBound base (layers a K).positive hSourceHeight
  have hSafeNew : (C.row r).PositiveBound (C.ordinaryContext.copyValue v) (topValue base s) c := by
    rw [← hCoord]
    by_cases hr : r < C.level
    · apply C.positiveBound_copy v hr ?_ hs hSafe b
      intro hBound
      have hAnc := C.root_ancestor_last (by omega : r+1 ≤ C.level)
      exact positiveBound_splice (rows base r).forest v hAnc hBound
    · exact C.positiveBound_copy_high v (by omega) hs hSafe b
  have hValue (q : Nat) (hq : M.height q = r+1) :
      C.ordinaryContext.copyValue v q = C.ordinaryContext.copyValue (topValue base) q := by
    change (rows base (r+1)).value (C.ordinaryContext.source0 q) =
      topValue base (C.ordinaryContext.source0 q)
    unfold topValue
    rw [(hHeight q).trans hq]
  have hPPos : 0 < C.ordinaryContext.copyValue v p := by
    rw [hValue p (hHeights.symm.trans hRow)]
    exact topValue_pos base ((layers a K).positive _)
  have hBound := hSafeNew p (Or.inr (Pseudo.parent_ancestor M hp)) hPPos
  rw [hValue p (hHeights.symm.trans hRow)] at hBound
  exact hBound

end OneY.Numeric

#print axioms OneY.TerminalCopy.Context.positiveBound_copy
#print axioms OneY.Numeric.positiveBound_splice
#print axioms OneY.Numeric.badAtTerminal_pseudoTopBound
