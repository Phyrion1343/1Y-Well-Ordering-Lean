import OneY.ExpansionOrder
import OneY.RootIndexed.ExpansionWellFounded
import ZeroY.Dynamics.Prefix
import YesMetaZFC.BMS.WellFoundedness

/-! # Actual 1-Y paths and the lexicographic order of a fixed descendant set

The order bridge uses the actual nested-prefix expansion theorem. Its only
well-foundedness input is that the actual nontrivial expansion step is
well-founded; no ancestor comparability or order embedding is assumed.
-/

namespace OneY.Numeric

abbrev Step := ZeroY.ExpansionStep expand
abbrev StrictDescent := Relation.TransGen Step

inductive ExpansionPath : ZeroY.Expr → ZeroY.Expr → Prop
  | refl (s : ZeroY.Expr) : ExpansionPath s s
  | tail {root middle : ZeroY.Expr} (prior : ExpansionPath root middle) (N : Nat) :
      ExpansionPath root (expand middle N)

namespace ExpansionPath

theorem single (s : ZeroY.Expr) (N : Nat) : ExpansionPath s (expand s N) := .tail (.refl _) N

theorem trans {a b c : ZeroY.Expr} (h : ExpansionPath a b) (g : ExpansionPath b c) :
    ExpansionPath a c := by
  induction g with
  | refl => exact h
  | tail prior N ih => exact .tail ih N

theorem eq_or_strictDescent {s t : ZeroY.Expr} (h : ExpansionPath s t) :
    t = s ∨ StrictDescent t s := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail middle prior N ih =>
      by_cases he : expand middle N = middle
      · rw [he]
        exact ih
      · have hStep : Step (expand middle N) middle := ⟨⟨N, rfl⟩, he⟩
        rcases ih with hEq | hPrev
        · subst middle
          exact Or.inr (.single hStep)
        · exact Or.inr (Relation.TransGen.trans (.single hStep) hPrev)

theorem eq_or_first_step {s t : ZeroY.Expr} (h : ExpansionPath s t) :
    t = s ∨ ∃ first, Step first s ∧ ExpansionPath first t := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail middle prior N ih =>
      rcases ih with he | ⟨first, hf, hr⟩
      · subst middle
        by_cases hn : expand s N = s
        · exact Or.inl hn
        · exact Or.inr ⟨expand s N, ⟨⟨N, rfl⟩, hn⟩, .refl _⟩
      · exact Or.inr ⟨first, hf, .tail hr N⟩

end ExpansionPath

theorem path_of_strictDescent {s t : ZeroY.Expr} (h : StrictDescent t s) : ExpansionPath s t := by
  induction h with
  | single h =>
      obtain ⟨⟨N, rfl⟩, _⟩ := h
      exact .single _ N
  | tail prior h ih =>
      obtain ⟨⟨N, he⟩, _⟩ := h
      exact (he ▸ ExpansionPath.single _ N).trans ih

theorem path_take (s : ZeroY.Expr) (n : Nat) : ExpansionPath s (s.take n) := by
  have aux : ∀ m, ∀ t : ZeroY.Expr, t.values.length = m → ExpansionPath t (t.take n) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro t hm
        by_cases hn : t.values.length ≤ n
        · rw [ZeroY.expr_take_of_length_le t n hn]
          exact .refl _
        · have hZero : expand t 0 = t.take (t.values.length-1) :=
            ZeroY.Expr.ext (expandValues_zero t.values t.legal)
          have hLen : (expand t 0).values.length = t.values.length-1 := by
            rw [hZero]
            simp only [ZeroY.Expr.take, List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
          have hNext := ih (expand t 0).values.length (by omega) (expand t 0) rfl
          have he : (expand t 0).take n = t.take n := by
            rw [hZero, ZeroY.expr_take_take, Nat.min_eq_left (by omega : n ≤ t.values.length-1)]
          rw [he] at hNext
          exact (ExpansionPath.single t 0).trans hNext
  exact aux s.values.length s rfl

theorem expand_reaches_earlier (s : ZeroY.Expr) {i j : Nat} (hij : i ≤ j) :
    ExpansionPath (expand s j) (expand s i) := by
  have he : (expand s j).take (expand s i).values.length = expand s i :=
    ZeroY.Expr.ext (expandValues_nested_take s.values s.legal hij)
  rw [← he]
  exact path_take _ _

theorem path_endpoints_comparable {s : ZeroY.Expr} (hs : Acc Step s) :
    ∀ {a b}, ExpansionPath s a → ExpansionPath s b →
      a = b ∨ StrictDescent a b ∨ StrictDescent b a := by
  induction hs with
  | intro s _ ih =>
      intro a b ha hb
      rcases ha.eq_or_first_step with he | ⟨p, hp, hap⟩
      · subst a
        rcases hb.eq_or_strictDescent with he | hb'
        · exact Or.inl he.symm
        · exact Or.inr (Or.inr hb')
      rcases hb.eq_or_first_step with he | ⟨q, hq, hbq⟩
      · subst b
        rcases ha.eq_or_strictDescent with he | ha'
        · exact Or.inl he
        · exact Or.inr (Or.inl ha')
      obtain ⟨i, hi⟩ := hp.1
      obtain ⟨j, hj⟩ := hq.1
      subst p
      subst q
      by_cases hij : i ≤ j
      · exact ih (expand s j) hq ((expand_reaches_earlier s hij).trans hap) hbq
      · exact ih (expand s i) hp hap ((expand_reaches_earlier s (by omega)).trans hbq)

theorem exprLt_of_step {s t : ZeroY.Expr} (h : Step t s) : ZeroY.ExprLt t s := by
  have hn : s.values ≠ [] := by
    intro he
    have hEmpty : s = ZeroY.Expr.empty := ZeroY.Expr.ext he
    subst s
    exact expansionStep_empty h
  obtain ⟨⟨N, rfl⟩, _⟩ := h
  exact expand_lt s N hn

theorem step_iff_nonempty {s t : ZeroY.Expr} :
    Step t s ↔ s.values ≠ [] ∧ ∃ N, expand s N = t := by
  constructor
  · intro h
    refine ⟨?_, h.1⟩
    intro he
    have hs : s = ZeroY.Expr.empty := ZeroY.Expr.ext he
    subst s
    exact expansionStep_empty h
  · rintro ⟨hs, N, hN⟩
    refine ⟨⟨N, hN⟩, ?_⟩
    intro he
    have hlt := expand_lt s N hs
    rw [hN, he] at hlt
    exact ZeroY.exprLt_irrefl _ hlt

theorem exprLt_of_strictDescent {s t : ZeroY.Expr} (h : StrictDescent t s) : ZeroY.ExprLt t s := by
  induction h with
  | single h => exact exprLt_of_step h
  | tail prior h ih => exact ZeroY.exprLt_trans ih (exprLt_of_step h)

theorem descendants_exprLt_iff (hWF : WellFounded Step) {root a b : ZeroY.Expr}
    (ha : ExpansionPath root a) (hb : ExpansionPath root b) :
    ZeroY.ExprLt a b ↔ StrictDescent a b := by
  constructor
  · intro hlt
    rcases path_endpoints_comparable (hWF.apply root) ha hb with he | hab | hba
    · subst a
      exact False.elim (ZeroY.exprLt_irrefl b hlt)
    · exact hab
    · exact False.elim (ZeroY.SeqLt.asymm hlt (exprLt_of_strictDescent hba))
  · exact exprLt_of_strictDescent

abbrev Descendant (root : ZeroY.Expr) := { s : ZeroY.Expr // ExpansionPath root s }

def DescendantLt {root : ZeroY.Expr} (a b : Descendant root) : Prop := ZeroY.ExprLt a.val b.val

theorem descendants_wellFounded (hWF : WellFounded Step) (root : ZeroY.Expr) :
    WellFounded (@DescendantLt root) :=
  ZeroY.wellFounded_of_relation_map (fun s : Descendant root => s.val)
    (fun {a b} hab => (descendants_exprLt_iff hWF a.property b.property).mp hab) hWF.transGen

open YesMetaZFC.BMS.StabilityFrame

theorem descendants_strictWellOrder (hWF : WellFounded Step) (root : ZeroY.Expr) :
    StrictWellOrder (Descendant root) DescendantLt where
  wellFounded := descendants_wellFounded hWF root
  transitive := fun h1 h2 => ZeroY.exprLt_trans h1 h2
  trichotomy := fun a b => by
    rcases ZeroY.exprLt_trichotomy a.val b.val with he | hab | hba
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr hba)

theorem expand_seed_succ (n : Nat) : expand (ZeroY.Expr.seed (n+1)) 1 = ZeroY.Expr.seed n := by
  let s := ZeroY.Expr.seed (n+1)
  have hSome : ∃ z, findBadRoot s.values s.legal (s.values.length-1) = some z := by
    cases hz : findBadRoot s.values s.legal (s.values.length-1) with
    | some z => exact ⟨z, rfl⟩
    | none =>
        have hp := (findBadRoot_none_iff s.values s.legal _).mp hz
        have hone := ofSequence_rootsOne s.values s.legal _ hp
        change n+1+1 = 1 at hone
        omega
  obtain ⟨z, hz⟩ := hSome
  have hbad := (findBadRoot_sound s.values s.legal _ hz).2
  have hleft := (rows (layers (rootedSequence s.values s.legal) z.layer).row z.row).forest.parent_left hbad.1
  have hz0 : z.column = 0 := by change z.column < 1 at hleft; omega
  have hlen : (expand s 1).values.length = 2 := by
    change (expandValues s.values s.legal 1).length = 2
    rw [expandValues_of_badRoot s.values s.legal 1 hz, reconstructedValues_length]
    simp [s, ZeroY.Expr.seed, hz0]
  apply ZeroY.Expr.ext
  apply List.ext_getElem?
  intro c
  by_cases hc0 : c = 0
  · subst c
    exact expandValues_prefix s.values s.legal 1 (show 0 < s.values.length-1 by change 0 < 1; decide)
  · by_cases hc1 : c = 1
    · subst c
      have hsuc := expandValues_first_seam_succ s.values s.legal 1 hz (by decide)
      change (expand s 1).values[1]?.getD 1+1 = n+1+1 at hsuc
      have h1 : 1 < (expand s 1).values.length := by omega
      rw [List.getElem?_eq_getElem h1] at hsuc
      simp only [Option.getD_some] at hsuc
      change (expand s 1).values[1]? = some (n+1)
      rw [List.getElem?_eq_getElem h1]
      congr 1
      omega
    · rw [List.getElem?_eq_none (show (expand s 1).values.length ≤ c by omega),
        List.getElem?_eq_none (show (ZeroY.Expr.seed n).values.length ≤ c by change 2 ≤ c; omega)]

theorem seed_reaches (i j : Nat) (hij : i ≤ j) :
    ExpansionPath (ZeroY.Expr.seed j) (ZeroY.Expr.seed i) := by
  induction j with
  | zero =>
      have he : i = 0 := by omega
      subst i
      exact .refl _
  | succ j ih =>
      by_cases he : i = j+1
      · subst i; exact .refl _
      · have hFirst := ExpansionPath.single (ZeroY.Expr.seed (j+1)) 1
        rw [expand_seed_succ] at hFirst
        exact hFirst.trans (ih (by omega))

def Generated (s : ZeroY.Expr) : Prop := ∃ n, ExpansionPath (ZeroY.Expr.seed n) s
abbrev GeneratedExpr := { s : ZeroY.Expr // Generated s }
def GeneratedLt (s t : GeneratedExpr) : Prop := ZeroY.ExprLt s.val t.val

/-- Adding the degenerate seed `(1,1)` does not enlarge the standard set:
it is already reached from `(1,2)`. Thus this is exactly generation from
the user-specified seeds `(1,m)` with `m ≥ 2`. -/
theorem generated_iff_nontrivial_seed (s : ZeroY.Expr) :
    Generated s ↔ ∃ n, ExpansionPath (ZeroY.Expr.seed (n+1)) s := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (seed_reaches n (n+1) (by omega)).trans hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n+1, hn⟩

theorem generated_exprLt_iff (hWF : WellFounded Step) (s t : GeneratedExpr) :
    GeneratedLt s t ↔ StrictDescent s.val t.val := by
  obtain ⟨i, hi⟩ := s.property
  obtain ⟨j, hj⟩ := t.property
  exact descendants_exprLt_iff hWF
    ((seed_reaches i (max i j) (Nat.le_max_left _ _)).trans hi)
    ((seed_reaches j (max i j) (Nat.le_max_right _ _)).trans hj)

theorem generated_strictWellOrder (hWF : WellFounded Step) :
    StrictWellOrder GeneratedExpr GeneratedLt where
  wellFounded := ZeroY.wellFounded_of_relation_map (fun s : GeneratedExpr => s.val)
    (fun {a b} hab => (generated_exprLt_iff hWF a b).mp hab) hWF.transGen
  transitive := fun h1 h2 => ZeroY.exprLt_trans h1 h2
  trichotomy := fun a b => by
    rcases ZeroY.exprLt_trichotomy a.val b.val with he | hab | hba
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr hba)

/-- Arbitrary choices of expansion indices cannot avoid the empty state
forever. No monotonicity or fixed rule for those choices is required. -/
theorem expansion_chain_reaches_empty (hWF : WellFounded Step) (chain : Nat → ZeroY.Expr)
    (hNext : ∀ n, ∃ N, chain (n+1) = expand (chain n) N) :
    ∃ n, (chain n).values = [] := by
  by_cases hEnd : ∃ n, (chain n).values = []
  · exact hEnd
  · have hNonempty : ∀ n, (chain n).values ≠ [] := fun n he => hEnd ⟨n, he⟩
    have hStep : ∀ n, Step (chain (n+1)) (chain n) := by
      intro n
      obtain ⟨N, hN⟩ := hNext n
      exact step_iff_nonempty.mpr ⟨hNonempty n, N, hN.symm⟩
    have hImpossible : ∀ s, Acc Step s → ∀ n, chain n = s → False := by
      intro s hs
      induction hs with
      | intro s _ ih =>
          intro n he
          have h := hStep n
          rw [he] at h
          exact ih (chain (n+1)) h (n+1) rfl
    exact False.elim (hImpossible (chain 0) (hWF.apply _) 0 rfl)

end OneY.Numeric

#print axioms OneY.Numeric.path_endpoints_comparable
#print axioms OneY.Numeric.descendants_exprLt_iff
#print axioms OneY.Numeric.descendants_wellFounded
#print axioms OneY.Numeric.expand_seed_succ
#print axioms OneY.Numeric.generated_strictWellOrder
#print axioms OneY.Numeric.expansion_chain_reaches_empty
