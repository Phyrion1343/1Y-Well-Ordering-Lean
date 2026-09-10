import OneY.Pseudo
import ZeroY.Forest.Blocker

/-! # Executable search for the first matching ancestor -/

namespace OneY.ParentForest

def firstMatch (F : ParentForest) (test : Nat → Bool) (c : Nat) : Option Nat :=
  match _hp : F.parent c with
  | none => none
  | some p => if test p then some p else firstMatch F test p
termination_by c
decreasing_by exact F.parent_left _hp

theorem firstMatch_of_none (F : ParentForest) (test : Nat → Bool) {c : Nat}
    (hp : F.parent c = none) : F.firstMatch test c = none := by
  rw [firstMatch]
  split <;> simp_all

theorem firstMatch_of_some (F : ParentForest) (test : Nat → Bool) {c p : Nat}
    (hp : F.parent c = some p) :
    F.firstMatch test c = if test p then some p else F.firstMatch test p := by
  rw [firstMatch]
  split <;> simp_all

theorem firstMatch_skipTo (F : ParentForest) (test : Nat → Bool) {a c : Nat}
    (ha : F.Ancestor a c)
    (hBetween : ∀ q, F.Ancestor q c → a < q → test q = false) :
    F.firstMatch test c = if test a then some a else F.firstMatch test a := by
  induction ha with
  | direct hp => exact F.firstMatch_of_some test hp
  | @step p c ha hp ih =>
      rw [F.firstMatch_of_some test hp, hBetween p (Ancestor.direct hp) ha.lt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (fun q hq hlt => hBetween q (hq.trans (Ancestor.direct hp)) hlt)

theorem firstMatch_eq_of_nearest (F : ParentForest) (test : Nat → Bool) {a c : Nat}
    (ha : F.Ancestor a c) (hTest : test a = true)
    (hMax : ∀ q, F.Ancestor q c → test q = true → q ≤ a) :
    F.firstMatch test c = some a := by
  rw [F.firstMatch_skipTo test ha (by
    intro q hq hlt
    cases ht : test q with
    | false => rfl
    | true => have := hMax q hq ht; omega), hTest]
  rfl

theorem firstMatch_some_spec (F : ParentForest) (test : Nat → Bool) {c p : Nat}
    (hp : F.firstMatch test c = some p) :
    F.Ancestor p c ∧ test p = true ∧ ∀ q, F.Ancestor q c → test q = true → q ≤ p := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hq : F.parent c with
      | none => rw [F.firstMatch_of_none test hq] at hp; contradiction
      | some q =>
          rw [F.firstMatch_of_some test hq] at hp
          by_cases hTest : test q = true
          · simp only [hTest] at hp
            have he : q = p := Option.some.inj hp
            subst p
            refine ⟨Ancestor.direct hq, hTest, ?_⟩
            intro z hz _
            rcases ZeroY.Forest.ancestor_eq_or_below_parent hq (ancestor_to_zeroY hz) with he | ha
            · omega
            · have := ZeroY.Forest.ancestor_lt F.parent_left ha; omega
          · simp only [hTest, ↓reduceIte] at hp
            obtain ⟨ha, htp, hmax⟩ := ih q (F.parent_left hq) hp
            refine ⟨ha.trans (Ancestor.direct hq), htp, ?_⟩
            intro z hz htz
            rcases ZeroY.Forest.ancestor_eq_or_below_parent hq (ancestor_to_zeroY hz) with he | hzq
            · subst z
              exact False.elim (hTest htz)
            · exact hmax z (ancestor_of_zeroY hzq) htz

theorem firstMatch_prefix_congr (F G : ParentForest) (test other : Nat → Bool) (n : Nat)
    (hParent : ∀ c, c < n → F.parent c = G.parent c)
    (hTest : ∀ c, c < n → test c = other c) {c : Nat} (hc : c < n) :
    F.firstMatch test c = G.firstMatch other c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => rw [F.firstMatch_of_none test hp, G.firstMatch_of_none other ((hParent c hc).symm.trans hp)]
      | some p =>
          have hlt := F.parent_left hp
          rw [F.firstMatch_of_some test hp, G.firstMatch_of_some other ((hParent c hc).symm.trans hp),
            hTest p (by omega), ih p hlt (by omega)]

end OneY.ParentForest

namespace OneY.Pseudo

theorem parent_eq_firstMatch (M : RootGeometry.RowMountain) {c : Nat} (hc : 0 < M.height c) :
    parent M c = (M.row (M.height c-1)).firstMatch (fun q => decide (M.height q ≤ M.height c)) c := by
  cases hp : parent M c with
  | none => have := (parent_none_iff M c).mp hp; omega
  | some p =>
      have hspec := (parent_some_iff M c p).mp hp
      symm
      apply ParentForest.firstMatch_eq_of_nearest _ _ hspec.2.1.1
      · simp only [decide_eq_true_eq]
        rcases hspec.2.1.2 with hh | hh <;> omega
      · intro q hq htest
        have all : ∀ {r a z}, (M.row r).Ancestor a z → r ≤ M.height a := by
          intro r a z ha
          induction ha with
          | direct hp => exact M.parent_endpoint hp
          | step _ _ ih => exact ih
        have hEndpoint := all hq
        simp only [decide_eq_true_eq] at htest
        exact hspec.2.2 q ⟨hq, by omega⟩

end OneY.Pseudo

#print axioms OneY.ParentForest.firstMatch_skipTo
#print axioms OneY.Pseudo.parent_eq_firstMatch
