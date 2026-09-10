import OneYTruth.InternalProducts

/-!
# An internal bounded step of the Tarski recursion

The step tests only the six actual diagram sets and an earlier truth
approximation. One explicit bounded Separation instance makes the next
approximation an internal set. Finite induction does not establish that
the entire omega family is internal; that further Collection obligation
is deliberately kept separate.
-/

namespace OneYTruth.BoundedEvaluation

open Constructible Constructible.Delta0Formula InternalClosure InternalProducts

universe u v

def Evaluates (D : Diagram.{u}) (S x : ZFSet.{u}) : Prop :=
  x ∈ D.trueAtoms ∨
  (∃ a ∈ D.nodes, ∃ b ∈ D.nodes,
    Godel.triple x a b ∈ D.implications ∧ (a ∈ S → b ∈ S)) ∨
  (x ∈ D.quantified ∧ ∀ a ∈ D.nodes, ZFSet.pair x a ∈ D.children → a ∈ S)

noncomputable def stepSet (D : Diagram.{u}) (S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : {x : ZFCarrier D.nodes // Evaluates D S x.val} => x.val.val)

theorem mem_stepSet_iff (D : Diagram.{u}) (S x : ZFSet.{u}) :
    x ∈ stepSet D S ↔ x ∈ D.nodes ∧ Evaluates D S x := by
  constructor
  · intro h
    obtain ⟨⟨⟨a, ha⟩, he⟩, hax⟩ := ZFSet.mem_range.mp h
    subst x
    exact ⟨ha, he⟩
  · rintro ⟨hx, he⟩
    exact ZFSet.mem_range.mpr ⟨⟨⟨x, hx⟩, he⟩, rfl⟩

def stepAt {n : Nat} (S nodes truths implications quantified children x : Fin n) :
    Delta0Formula n :=
  .disj (.mem x truths)
    (.disj
      (.boundedEx nodes (.boundedEx nodes.castSucc
        (.conj (tripleMemAt implications.castSucc.castSucc x.castSucc.castSucc
          (Fin.last n).castSucc (Fin.last (n + 1)))
          (.imp (.mem (Fin.last n).castSucc S.castSucc.castSucc)
            (.mem (Fin.last (n + 1)) S.castSucc.castSucc)))))
      (.conj (.mem x quantified)
        (.boundedAll nodes (.imp
          (pairMemAt children.castSucc x.castSucc (Fin.last n))
          (.mem (Fin.last n) S.castSucc)))))

theorem satisfies_stepAt {n : Nat} (S nodes truths implications quantified children x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (stepAt S nodes truths implications quantified children x) s ↔
      s x ∈ s truths ∨
      (∃ a ∈ s nodes, ∃ b ∈ s nodes,
        Godel.triple (s x) a b ∈ s implications ∧ (a ∈ s S → b ∈ s S)) ∨
      (s x ∈ s quantified ∧ ∀ a ∈ s nodes,
        ZFSet.pair (s x) a ∈ s children → a ∈ s S) := by
  simp only [stepAt, satisfies_disj, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_tripleMemAt, satisfies_pairMemAt, snoc_last, snoc_castSucc]

/-- Coordinates: S,nodes,atoms,trueAtoms,implications,quantified,children,x. -/
def stepFormula : Delta0Formula 8 := stepAt 0 1 3 4 5 6 7

theorem satisfies_stepFormula (D : Diagram.{u}) (S x : ZFSet.{u}) :
    Satisfies ZFMem stepFormula (Constructible.snoc (parameters D S) x) ↔ Evaluates D S x := by
  rw [stepFormula, satisfies_stepAt]
  rfl

def mixedStepFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I stepFormula

theorem mixedStepFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedStepFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I stepFormula

theorem stepSet_mem_of_separation {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedStepFormula k I))
    (D : Diagram.{u}) (S : ZFSet.{u}) (hp : ∀ i, parameters D S i ∈ V) :
    stepSet D S ∈ V := by
  have hsource : ZFSet.range (Subtype.val : ZFCarrier D.nodes → ZFSet.{u}) ∈ V := by
    rw [range_carrier_val_eq]
    exact hp 1
  apply filtered_range_mem hV N (mixedStepFormula k I) hSep
    (fun i => ⟨parameters D S i, hp i⟩) Subtype.val
    (fun x : ZFCarrier D.nodes => Evaluates D S x.val) hsource
  intro x hx
  rw [mixedStepFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc (fun i => (⟨parameters D S i, hp i⟩ : ZFCarrier V)) ⟨x.val, hx⟩) =
      Constructible.snoc (parameters D S) x.val := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_stepFormula D S x.val

noncomputable def iterate (D : Diagram.{u}) : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => stepSet D (iterate D n)

theorem iterate_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedStepFormula k I))
    (hempty : (∅ : ZFSet.{u}) ∈ V) (D : Diagram.{u})
    (hD : ∀ i, parameters D ∅ i ∈ V) (n : Nat) : iterate D n ∈ V := by
  induction n with
  | zero => exact hempty
  | succ n ih =>
    apply stepSet_mem_of_separation hV N hmem hSep D (iterate D n)
    intro i
    fin_cases i
    · exact ih
    · exact hD 1
    · exact hD 2
    · exact hD 3
    · exact hD 4
    · exact hD 5
    · exact hD 6

/-- Coordinates: S,nodes,atoms,trueAtoms,implications,quantified,children,T. -/
def stepGraphFormula : Delta0Formula 8 :=
  .conj (subsetAt 7 1)
    (.boundedAll 1 (.biimp (.mem 8 7) (stepAt 0 1 3 4 5 6 8)))

theorem satisfies_stepGraphFormula (D : Diagram.{u}) (S T : ZFSet.{u}) :
    Satisfies ZFMem stepGraphFormula (Constructible.snoc (parameters D S) T) ↔
      T = stepSet D S := by
  simp only [stepGraphFormula, Satisfies, satisfies_subsetAt, satisfies_boundedAll,
    satisfies_biimp, satisfies_stepAt]
  change (T ⊆ D.nodes ∧ ∀ x ∈ D.nodes, x ∈ T ↔ Evaluates D S x) ↔ T = stepSet D S
  constructor
  · rintro ⟨hsub, hstep⟩
    apply ZFSet.ext
    intro x
    rw [mem_stepSet_iff]
    exact ⟨fun hx => ⟨hsub hx, (hstep x (hsub hx)).mp hx⟩,
      fun ⟨hx, he⟩ => (hstep x hx).mpr he⟩
  · intro h
    subst T
    exact ⟨fun x hx => (mem_stepSet_iff D S x).mp hx |>.1,
      fun x hx => (mem_stepSet_iff D S x).trans (and_iff_right hx)⟩

theorem satisfies_stepGraphFormula_tuple (s : Tuple ZFSet.{u} 8) :
    Satisfies ZFMem stepGraphFormula s ↔
      s 7 = stepSet ⟨s 1, s 2, s 3, s 4, s 5, s 6⟩ (s 0) := by
  have h := satisfies_stepGraphFormula ⟨s 1, s 2, s 3, s 4, s 5, s 6⟩ (s 0) (s 7)
  have heq : Constructible.snoc (parameters ⟨s 1, s 2, s 3, s 4, s 5, s 6⟩ (s 0)) (s 7) = s := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  exact h

end OneYTruth.BoundedEvaluation
