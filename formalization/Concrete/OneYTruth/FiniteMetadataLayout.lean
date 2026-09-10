import OneYTruth.FiniteAmbientTuple
import OneYTruth.FiniteTupleSplit

/-! Actual metadata and label slots used for one simultaneous reflection.
All metadata precede the labels and are part of the fixed parameter tuple. -/
namespace OneYTruth.FiniteLabelAssembly
open Constructible OneY.RootIndexed
universe u v

def labelSlots (m n : Nat) (anchor : Fin m) : Fin (n+1) → Fin (m+n) :=
  Fin.snoc (Fin.natAdd m) (Fin.castAdd n anchor)

@[simp] theorem labelSlots_label (m n : Nat) (anchor : Fin m) (i : Fin n) :
    labelSlots m n anchor i.castSucc = Fin.natAdd m i := by simp [labelSlots]

noncomputable def fullAmbient {β : Ordinal.{u}} {m : Nat} (G : Diagram)
    (pars : Fin m → ZFCarrier (LStageZF β)) (f : Nat → Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) : Fin (m+G.size) → ZFCarrier (LStageZF β) :=
  Fin.append pars (fun i => ordinalCarrier (f i.val) (hb i.val i.isLt))

@[simp] theorem fullAmbient_label {β : Ordinal.{u}} {m : Nat} (G : Diagram)
    (pars : Fin m → ZFCarrier (LStageZF β)) (f : Nat → Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (i : Fin G.size) :
    (fullAmbient G pars f hb (Fin.natAdd m i)).val = (f i.val).toZFSet := by
  simp [fullAmbient,ordinalCarrier]

theorem fullAmbient_slots {β : Ordinal.{u}} {m : Nat} (G : Diagram)
    (pars : Fin m → ZFCarrier (LStageZF β)) (f : Nat → Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (anchor : Fin m) :
    fullAmbient G pars f hb ∘ labelSlots m G.size anchor = ambientTuple G f hb (pars anchor) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Function.comp_def,labelSlots,fullAmbient,ambientTuple]
  · simp [Function.comp_def,labelSlots,fullAmbient,ambientTuple]

noncomputable def fullFixed {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF (f cut))) : Fin (m+cut) → ZFCarrier (LStageZF (f cut)) :=
  Fin.append pars (fixedPrefix hf cut hc)

theorem fullAmbient_prefix {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) {β : Ordinal.{u}}
    (hb : Bounded (· < ·) G.size f β) {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF (f cut))) :
    let inc := Auxiliary.inclusion (LStageZF_mono (hb cut hc).le)
    prefixTuple (show m+cut ≤ m+G.size by omega) (fullAmbient G (inc ∘ pars) f hb) =
      inc ∘ fullFixed hf cut hc pars := by
  dsimp only
  funext i
  induction i using Fin.addCases with
  | left i =>
      change fullAmbient G _ f hb (Fin.castAdd G.size i) = _
      simp [fullAmbient,fullFixed]
  | right i =>
      change fullAmbient G _ f hb (Fin.natAdd m ⟨i.val,i.isLt.trans hc⟩) = _
      simp only [fullAmbient,fullFixed,Function.comp_apply,Fin.append_right]
      rfl

theorem fixed_full_label {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF (f cut)))
    (q : Fin (m+G.size) → ZFCarrier (LStageZF (f cut)))
    (hq : prefixTuple (show m+cut ≤ m+G.size by omega) q = fullFixed hf cut hc pars)
    (i : Fin G.size) (hi : i.val < cut) :
    (q (Fin.natAdd m i)).val = (f i.val).toZFSet := by
  have h := congrFun hq (Fin.natAdd m ⟨i.val,hi⟩)
  change q (Fin.natAdd m i) = Fin.append pars (fixedPrefix hf cut hc) (Fin.natAdd m ⟨i.val,hi⟩) at h
  rw [Fin.append_right] at h
  exact congrArg Subtype.val h

theorem fixed_full_metadata {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF (f cut)))
    (q : Fin (m+G.size) → ZFCarrier (LStageZF (f cut)))
    (hq : prefixTuple (show m+cut ≤ m+G.size by omega) q = fullFixed hf cut hc pars)
    (i : Fin m) : q (Fin.castAdd G.size i) = pars i := by
  have h := congrFun hq (Fin.castAdd cut i)
  change q (Fin.castAdd G.size i) = Fin.append pars (fixedPrefix hf cut hc) (Fin.castAdd cut i) at h
  simpa using h

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.fullAmbient_prefix
#print axioms OneYTruth.FiniteLabelAssembly.fixed_full_label


