import OneY.Extraction
import ZeroY.Forest.Comparison
import ZeroY.Expansion

/-! # Locality of the actual inherited mountain construction

Appending or deleting columns on the right cannot change the construction
to their left. All root, row, and extraction data here are computed.
-/

namespace OneY.ParentForest

theorem root_prefix_congr (F G : ParentForest) (n : Nat)
    (h : ∀ c, c < n → F.parent c = G.parent c) :
    ∀ c, c < n → F.root c = G.root c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro hc
      cases hp : F.parent c with
      | none =>
          rw [F.root_of_parent_none hp, G.root_of_parent_none ((h c hc).symm.trans hp)]
      | some p =>
          rw [F.root_of_parent_some hp, G.root_of_parent_some ((h c hc).symm.trans hp)]
          exact ih p (F.parent_left hp) (by have := F.parent_left hp; omega)

theorem ancestor_prefix_forward (F G : ParentForest) (n : Nat)
    (h : ∀ c, c < n → F.parent c = G.parent c)
    {a c : Nat} (ha : F.Ancestor a c) (hc : c < n) : G.Ancestor a c := by
  induction ha with
  | direct hp => exact .direct ((h _ hc).symm.trans hp)
  | step ha hp ih =>
      exact .step (ih (by have := F.parent_left hp; omega)) ((h _ hc).symm.trans hp)

theorem ancestor_prefix_iff (F G : ParentForest) (n : Nat)
    (h : ∀ c, c < n → F.parent c = G.parent c) {a c : Nat} (hc : c < n) :
    F.Ancestor a c ↔ G.Ancestor a c :=
  ⟨fun ha => ancestor_prefix_forward F G n h ha hc,
    fun ha => ancestor_prefix_forward G F n (fun c hc => (h c hc).symm) ha hc⟩

end OneY.ParentForest

namespace OneY.Pseudo

theorem parent_prefix_congr (M N : RootGeometry.RowMountain) (n : Nat)
    (hH : ∀ c, c < n → M.height c = N.height c)
    (hP : ∀ r c, c < n → (M.row r).parent c = (N.row r).parent c)
    {c : Nat} (hc : c < n) : parent M c = parent N c := by
  unfold parent
  rw [hH c hc]
  split
  · rfl
  · apply ZeroY.Forest.greatestBelow?_congr
    intro p hp
    unfold eligible
    rw [hH c hc, hH p (by omega)]
    rw [YesMetaZFC.BMS.ancestorChain_congr_below (M.row (N.height c-1)).parent_left
      (fun i hi => hP (N.height c-1) i (by omega)) (Nat.le_refl c)]

end OneY.Pseudo

namespace OneY.Numeric

theorem restrictedParent_agreesBelow (F G : ParentForest) (v w : Nat → Nat)
    (n : Nat) (hF : ∀ c, c < n → F.parent c = G.parent c)
    (hV : ∀ c, c < n → v c = w c) {c : Nat} (hc : c < n) :
    restrictedParent F v c = restrictedParent G w c := by
  unfold restrictedParent
  rw [YesMetaZFC.BMS.ancestorChain_congr_below F.parent_left
    (fun i hi => hF i (by omega)) (Nat.le_refl c)]
  apply ZeroY.Forest.greatestBelow?_congr
  intro p hp
  rw [hV p (by omega), hV c hc]

def Row.AgreesBelow (a b : Row) (n : Nat) : Prop :=
  (∀ c, c < n → a.value c = b.value c) ∧
    (∀ c, c < n → a.forest.parent c = b.forest.parent c)

theorem Row.AgreesBelow.difference {a b : Row} {n : Nat} (h : a.AgreesBelow b n)
    {c : Nat} (hc : c < n) : a.difference c = b.difference c := by
  unfold Row.difference
  rw [← h.2 c hc]
  cases hp : a.forest.parent c with
  | none => rfl
  | some p =>
      change a.value c-a.value p = b.value c-b.value p
      rw [h.1 c hc, h.1 p (by have := a.forest.parent_left hp; omega)]

theorem Row.AgreesBelow.next {a b : Row} {n : Nat} (h : a.AgreesBelow b n) :
    a.next.AgreesBelow b.next n :=
  ⟨fun _ hc => h.difference hc,
    fun _ hc => restrictedParent_agreesBelow _ _ _ _ n h.2
      (fun _ hc => h.difference hc) hc⟩

theorem Row.AgreesBelow.rows {a b : Row} {n : Nat} (h : a.AgreesBelow b n) (r : Nat) :
    (Numeric.rows a r).AgreesBelow (Numeric.rows b r) n := by
  induction r with
  | zero => exact h
  | succ r ih => exact ih.next

theorem Row.AgreesBelow.height {a b : Row} {n : Nat} (h : a.AgreesBelow b n)
    {c : Nat} (hc : c < n) : Numeric.height a c = Numeric.height b c := by
  unfold Numeric.height topSearch
  rw [h.1 c hc]
  congr 1
  apply ZeroY.Forest.greatestBelow?_congr
  intro r hr
  rw [(h.rows r).1 c hc]

theorem Row.AgreesBelow.topValue {a b : Row} {n : Nat} (h : a.AgreesBelow b n)
    {c : Nat} (hc : c < n) : Numeric.topValue a c = Numeric.topValue b c := by
  unfold Numeric.topValue
  rw [h.height hc]
  exact (h.rows _).1 c hc

theorem Row.AgreesBelow.rawExtract {a b : Row} {n : Nat} (h : a.AgreesBelow b n)
    (ha : ∀ c, 0 < a.value c) (hb : ∀ c, 0 < b.value c) :
    (Numeric.rawExtract a ha).AgreesBelow (Numeric.rawExtract b hb) n := by
  constructor
  · exact fun _ hc => h.topValue hc
  · intro c hc
    apply restrictedParent_agreesBelow _ _ _ _ n
    · intro q hq
      exact Pseudo.parent_prefix_congr (mountain a ha) (mountain b hb) n
        (fun _ hc => h.height hc) (fun r _ hc => (h.rows r).2 _ hc) hq
    · exact fun _ hc => h.topValue hc
    · exact hc

theorem layers_agree_below (a b : RootedRow) {n : Nat}
    (h : a.row.AgreesBelow b.row n) (k : Nat) :
    (layers a k).row.AgreesBelow (layers b k).row n := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.rawExtract (layers a k).positive (layers b k).positive

theorem ofSequence_agreesBelow (s t : List Nat) (n : Nat)
    (h : ∀ c, c < n → s[c]? = t[c]?) : (ofSequence s).AgreesBelow (ofSequence t) n := by
  constructor
  · intro c hc
    change s[c]?.getD 1 = t[c]?.getD 1
    rw [h c hc]
  · intro c hc
    apply restrictedParent_agreesBelow _ _ _ _ n (fun _ _ => rfl)
    · intro q hq
      exact congrArg (fun v : Option Nat => v.getD 1) (h q hq)
    · exact hc

theorem ofSequence_take_agreesBelow (s : List Nat) (n : Nat) :
    (ofSequence s).AgreesBelow (ofSequence (s.take n)) n :=
  ofSequence_agreesBelow s (s.take n) n
    (fun _ hc => (List.getElem?_take_of_lt hc).symm)

theorem sequence_take_layers_agree (s : List Nat) (hs : ZeroY.Legal s) (n k : Nat) :
    (layers (rootedSequence s hs) k).row.AgreesBelow
      (layers (rootedSequence (s.take n) (ZeroY.legal_take hs n)) k).row n :=
  layers_agree_below _ _ (ofSequence_take_agreesBelow s n) k

end OneY.Numeric

#print axioms OneY.Numeric.Row.AgreesBelow.rows
#print axioms OneY.Numeric.Row.AgreesBelow.topValue
#print axioms OneY.Numeric.sequence_take_layers_agree
