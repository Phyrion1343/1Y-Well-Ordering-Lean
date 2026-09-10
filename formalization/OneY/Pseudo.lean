import OneY.RootGeometry
import OneY.ForestBridge

/-!
# The actual geometric pseudo-parent computation

Search the last finite parent row below a column's top, selecting the
nearest ancestor whose height is the same or one smaller. The search is
finite and executable; its existence and height properties are proved.
-/

namespace OneY.Pseudo

open RootGeometry YesMetaZFC.BMS

def Candidate (M : RowMountain) (c p : Nat) : Prop :=
  (M.row (M.height c - 1)).Ancestor p c ∧
    (M.height p = M.height c ∨ M.height p + 1 = M.height c)

def eligible (M : RowMountain) (c p : Nat) : Bool :=
  (ancestorChain (M.row (M.height c - 1)).parent c c).contains p &&
    decide (M.height p = M.height c ∨ M.height p + 1 = M.height c)

theorem eligible_iff (M : RowMountain) (c p : Nat) :
    eligible M c p = true ↔ Candidate M c p := by
  unfold eligible Candidate
  rw [Bool.and_eq_true, decide_eq_true_eq,
    ZeroY.Forest.ancestorChain_contains_iff (M.row (M.height c - 1)).parent_left]
  exact and_congr (ParentForest.ancestor_iff_zeroY _ _ _).symm Iff.rfl

def parent (M : RowMountain) (c : Nat) : Option Nat :=
  if M.height c = 0 then none else greatestBelow? c (eligible M c)

theorem parent_some_iff (M : RowMountain) (c p : Nat) :
    parent M c = some p ↔
      0 < M.height c ∧ Candidate M c p ∧
        ∀ q, Candidate M c q → q ≤ p := by
  unfold parent
  by_cases hz : M.height c = 0
  · simp [hz]
  · rw [if_neg hz, greatestBelow?_eq_some_iff]
    simp only [eligible_iff]
    constructor
    · rintro ⟨_, hCand, hMax⟩
      exact ⟨by omega, hCand, fun q hq => hMax q hq.1.lt hq⟩
    · rintro ⟨_, hCand, hMax⟩
      exact ⟨hCand.1.lt, hCand, fun q _ hq => hMax q hq⟩

theorem parent_left (M : RowMountain) {c p : Nat} (hp : parent M c = some p) : p < c :=
  ((parent_some_iff M c p).mp hp).2.1.1.lt

theorem parent_height (M : RowMountain) {c p : Nat} (hp : parent M c = some p) :
    M.height p = M.height c ∨ M.height p + 1 = M.height c :=
  ((parent_some_iff M c p).mp hp).2.1.2

theorem parent_ancestor (M : RowMountain) {c p : Nat} (hp : parent M c = some p) :
    (M.row (M.height c - 1)).Ancestor p c :=
  ((parent_some_iff M c p).mp hp).2.1.1

theorem candidate_exists (M : RowMountain) {c : Nat} (hc : 0 < M.height c) :
    ∃ p, Candidate M c p := by
  let r := M.height c - 1
  have hr : r < M.height c := by dsimp [r]; omega
  have hlt := M.rootAt_lt hr
  have hh := M.root_height (Nat.le_of_lt hr)
  refine ⟨M.rootAt r c, ?_, Or.inr (by omega)⟩
  rcases (M.row r).root_ancestor_or_eq c with ha | he
  · exact ha
  · change M.rootAt r c = c at he
    omega

theorem parent_none_iff (M : RowMountain) (c : Nat) :
    parent M c = none ↔ M.height c = 0 := by
  constructor
  · intro hp
    by_cases hz : M.height c = 0
    · exact hz
    · obtain ⟨p, hCand⟩ := candidate_exists M (c := c) (by omega)
      have hs : greatestBelow? c (eligible M c) = none := by
        simpa only [parent, if_neg hz] using hp
      have hNo := greatestBelow?_eq_none_iff.mp hs p hCand.1.lt
      have hYes := (eligible_iff M c p).mpr hCand
      rw [hYes] at hNo
      cases hNo
  · intro hz
    simp only [parent, hz, if_pos]

def forest (M : RowMountain) : ParentForest where
  parent := parent M
  parent_left := fun hp => parent_left M hp

theorem ancestor_height_le (M : RowMountain) {a c : Nat}
    (h : (forest M).Ancestor a c) : M.height a ≤ M.height c := by
  induction h with
  | direct hp =>
      have hh := parent_height M hp
      omega
  | step _ hp ih =>
      have hh := parent_height M hp
      omega

theorem root_height_zero (M : RowMountain) (c : Nat) :
    M.height ((forest M).root c) = 0 := by
  exact (parent_none_iff M _).mp ((forest M).parent_root c)

theorem same_height_ancestor (M : RowMountain) {a c : Nat}
    (h : (forest M).Ancestor a c) (heq : M.height a = M.height c) :
    (M.row (M.height c - 1)).Ancestor a c := by
  revert heq
  induction h with
  | direct hp =>
      intro _
      exact parent_ancestor M hp
  | @step p c ha hp ih =>
      intro heq
      have hAP := ancestor_height_le M ha
      have hPC := parent_height M hp
      have hSame : M.height p = M.height c := by omega
      have hFirst := ih (by omega)
      rw [hSame] at hFirst
      exact hFirst.trans (parent_ancestor M hp)

end OneY.Pseudo

#print axioms OneY.Pseudo.parent_none_iff
#print axioms OneY.Pseudo.parent_height
#print axioms OneY.Pseudo.root_height_zero
#print axioms OneY.Pseudo.same_height_ancestor
