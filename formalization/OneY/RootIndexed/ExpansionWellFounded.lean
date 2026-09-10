import OneY.ExpansionCanonical
import OneY.RootIndexed.ActualScheme
import ZeroY.Transport

/-! # Actual expansion is well-founded under the semantic reflection interface

All mountain copying, numerical rebuilding, extraction, and finite diagram
transport are proved for `Numeric.expand`. Only the label order, the semantic
finite reflection principle, and initial finite representations are parameters.
The empty expression is handled as a terminal state, without requiring a label
below a least endpoint.
-/

namespace OneY.Numeric

theorem sequenceBound_take_le (s : List Nat) (n : Nat) :
    sequenceBound (s.take n) ≤ sequenceBound s := by
  have hm : ZeroY.maxValue (s.take n) ≤ ZeroY.maxValue s := by
    apply (ZeroY.maxValue_le_iff _ _).mpr
    intro v hv
    exact ZeroY.le_maxValue (List.mem_of_mem_take hv)
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hm (Nat.le_max_right _ _)⟩

theorem expand_empty (N : Nat) : expand ZeroY.Expr.empty N = ZeroY.Expr.empty := by
  apply ZeroY.Expr.ext
  have hp : (ofSequence []).forest.parent 0 = none := by
    cases hp : (ofSequence []).forest.parent 0 with
    | none => rfl
    | some p => have h := (ofSequence []).forest.parent_left hp; omega
  exact expandValues_of_no_parent [] ZeroY.Expr.empty.legal N hp

theorem expansionStep_empty {t : ZeroY.Expr} :
    ¬ZeroY.ExpansionStep expand t ZeroY.Expr.empty := by
  rintro ⟨⟨N, hN⟩, hne⟩
  rw [expand_empty] at hN
  exact hne hN.symm

theorem expansionStep_empty_accessible : Acc (ZeroY.ExpansionStep expand) ZeroY.Expr.empty :=
  Acc.intro _ (fun _ h => False.elim (expansionStep_empty h))

end OneY.Numeric

namespace OneY.RootIndexed

universe u

open Numeric

variable {α : Type u}

def exprDiagram (s : ZeroY.Expr) : Diagram :=
  sequenceDiagram s.values s.legal (sequenceBound s.values)

theorem expand_lastRepresentation_lower
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (reflection : FiniteReflection lt D R)
    (s : ZeroY.Expr) (N : Nat) (beta : α)
    (hRep : LastRepresentation lt D R (exprDiagram s) beta)
    (hNonempty : 0 < (expand s N).values.length) :
    ∃ b, lt b beta ∧ LastRepresentation lt D R (exprDiagram (expand s N)) b := by
  obtain ⟨hs, f, hF, hLast⟩ := hRep
  have hs' : 0 < s.values.length := hs
  cases hz : findBadRoot s.values s.legal (s.values.length-1) with
  | none =>
      have he := expandValues_of_no_parent s.values s.legal N
        ((findBadRoot_none_iff _ _ _).mp hz)
      have hTake : exprDiagram (expand s N) =
          sequenceDiagram (s.values.take (s.values.length-1))
            (ZeroY.legal_take s.legal _) (sequenceBound (s.values.take (s.values.length-1))) := by
        unfold exprDiagram
        change sequenceDiagram (expandValues s.values s.legal N) _ _ = _
        rw [show sequenceBound (expand s N).values =
          sequenceBound (s.values.take (s.values.length-1)) from congrArg sequenceBound he]
        exact sequenceDiagram_eq_of_values_eq _ _ he _
      have hPref : (exprDiagram (expand s N)).IsPrefix (exprDiagram s) := by
        rw [hTake]
        exact sequenceDiagram_take_isPrefix _ _ _ _ _ (sequenceBound_take_le _ _)
      refine proper_prefix_lowers_last_label lt D R hPref ?_ hNonempty beta
        ⟨hs, f, hF, hLast⟩
      change (expandValues s.values s.legal N).length < s.values.length
      rw [he, List.length_take]
      omega
  | some z =>
      have hbad := (findBadRoot_sound s.values s.legal _ hz).2
      have hK := (findBadRoot_sound s.values s.legal _ hz).1
      have hSize : s.values.length-1+1 = s.values.length := by omega
      have hOld : Representation lt D R
          (mountainDiagram (sequenceBound s.values) (s.values.length-1+1)
            (originalMountain (rootedSequence s.values s.legal))) f := by
        rw [hSize]
        exact hF
      obtain ⟨g, hg, hb⟩ := copied_diagrams_bounded lt D R hTrans hStrict hWeak reflection
        (rootedSequence s.values s.legal) hbad (sequenceBound s.values) hK f hOld N
      have hp := expandValues_diagram_of_badRoot s.values s.legal N
        (sequenceBound (expand s N).values) hz
      have hNew : Representation lt D R (exprDiagram (expand s N)) g :=
        representation_prefix lt D R hp g hg
      have hBound : Bounded lt (exprDiagram (expand s N)).size g beta := by
        intro i hi
        rw [← hLast]
        exact hb i (Nat.lt_of_lt_of_le hi hp.1)
      exact last_label_of_bounded_representation lt D R hNonempty g beta hNew hBound

theorem expansion_accessible_of_lastRepresentation
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (reflection : FiniteReflection lt D R)
    {beta : α} (hAcc : Acc lt beta) :
    ∀ s, LastRepresentation lt D R (exprDiagram s) beta →
      Acc (ZeroY.ExpansionStep expand) s := by
  induction hAcc with
  | intro beta _ ih =>
      intro s hRep
      apply Acc.intro s
      intro t hStep
      obtain ⟨⟨N, hN⟩, _⟩ := hStep
      by_cases ht : t.values = []
      · have he : t = ZeroY.Expr.empty := ZeroY.Expr.ext ht
        rw [he]
        exact expansionStep_empty_accessible
      · have hPos : 0 < t.values.length := List.length_pos_iff.mpr ht
        obtain ⟨b, hb, hNew⟩ := expand_lastRepresentation_lower lt D R hTrans hStrict hWeak
          reflection s N beta hRep (hN ▸ hPos)
        exact ih b hb t (hN ▸ hNew)

/-- This theorem has no geometric, canonicality, or layer-transport premises.
The remaining parameters belong entirely to the intended semantic label model. -/
theorem actual_expansion_wellFounded
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (hWF : WellFounded lt)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (reflection : FiniteReflection lt D R)
    (initial : ∀ s : ZeroY.Expr, ∃ f, Representation lt D R (exprDiagram s) f) :
    WellFounded (ZeroY.ExpansionStep expand) := by
  constructor
  intro s
  by_cases hs : s.values = []
  · have he : s = ZeroY.Expr.empty := ZeroY.Expr.ext hs
    rw [he]
    exact expansionStep_empty_accessible
  · obtain ⟨f, hf⟩ := initial s
    have hp : 0 < (exprDiagram s).size := List.length_pos_iff.mpr hs
    exact expansion_accessible_of_lastRepresentation lt D R hTrans hStrict hWeak reflection
      (hWF.apply (f (s.values.length-1))) s ⟨hp, f, hf, rfl⟩

end OneY.RootIndexed

#print axioms OneY.RootIndexed.expand_lastRepresentation_lower
#print axioms OneY.RootIndexed.actual_expansion_wellFounded
