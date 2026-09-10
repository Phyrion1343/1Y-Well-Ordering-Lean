import OneYTruth.FiniteQuerySemantics
import OneYTruth.ConstructibleCodes

/-! The only fixed set parameters of the finite reflection matrix are
omega, the empty set, and the finitely many layer numbers occurring in
the diagram and its endpoint demands. They all belong to every adequate
stage. The current endpoint ordinal is not one of these parameters. -/

namespace OneYTruth.ActualDiagramQueries

open Constructible Constructible.FiniteSequenceZF OneY.RootIndexed
open RootSemantics FiniteLabelAssembly

universe u

def tags (G : Diagram) (needs : List TopAtom) : List Nat :=
  G.atoms.map Atom.layer ++ needs.map TopAtom.layer

theorem atom_tag {G : Diagram} {needs : List TopAtom} {e : Atom} (he : e ∈ G.atoms) :
    e.layer ∈ tags G needs := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem need_tag {G : Diagram} {needs : List TopAtom} {d : TopAtom} (hd : d ∈ needs) :
    d.layer ∈ tags G needs := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨d,hd,rfl⟩)

def arity (ts : List Nat) : Nat := 2 + ts.length

def omegaIndex (ts : List Nat) : Fin (arity ts) := Fin.castAdd ts.length 0
def zeroIndex (ts : List Nat) : Fin (arity ts) := Fin.castAdd ts.length 1

def natIndex (ts : List Nat) (k : Nat) : Fin (arity ts) :=
  if hk : k ∈ ts then Fin.natAdd 2 ⟨ts.idxOf k,List.idxOf_lt_length_iff.mpr hk⟩
  else zeroIndex ts

noncomputable def metadata {α : Ordinal.{u}} (hα : Adequate α) (ts : List Nat) :
    Fin (arity ts) → ZFCarrier (LStageZF α) :=
  Fin.append
    ![⟨Ordinal.omega0.toZFSet,ordinal_toZFSet_mem_LStageZF_of_lt hα.1⟩,
      ⟨∅,by simpa [natCode] using natCode_mem_LStageZF_of_isSuccLimit hα.2.1 0⟩]
    (fun i => ⟨natCode (ts.get i),natCode_mem_LStageZF_of_isSuccLimit hα.2.1 _⟩)

structure MetadataCorrect {α : Ordinal.{u}} (ts : List Nat)
    (pars : Fin (arity ts) → ZFCarrier (LStageZF α)) : Prop where
  omega : (pars (omegaIndex ts)).val = Ordinal.omega0.toZFSet
  zero : (pars (zeroIndex ts)).val = ∅
  nat : ∀ k ∈ ts, (pars (natIndex ts k)).val = natCode k

theorem metadata_correct {α : Ordinal.{u}} (hα : Adequate α) (ts : List Nat) :
    MetadataCorrect ts (metadata hα ts) := by
  refine ⟨rfl,rfl,?_⟩
  intro k hk
  have hi : natIndex ts k = Fin.natAdd 2 ⟨ts.idxOf k,List.idxOf_lt_length_iff.mpr hk⟩ := by
    simp only [natIndex,hk,↓reduceDIte]
    apply Fin.ext
    rfl
  rw [hi]
  simp only [metadata,Fin.append_right]
  exact congrArg natCode (List.idxOf_get _)

theorem MetadataCorrect.inclusion {α β : Ordinal.{u}} {ts : List Nat}
    {pars : Fin (arity ts) → ZFCarrier (LStageZF α)} (h : MetadataCorrect ts pars)
    (hab : α ≤ β) :
    MetadataCorrect ts (Auxiliary.inclusion (LStageZF_mono hab) ∘ pars) :=
  ⟨h.omega,h.zero,h.nat⟩

theorem MetadataCorrect.at_omega {G : Diagram} {needs : List TopAtom}
    {cut : Nat} {f : Nat → Ordinal.{u}} {β : Ordinal.{u}}
    {pars : Fin (arity (tags G needs)) → ZFCarrier (LStageZF β)}
    (h : MetadataCorrect (tags G needs) pars)
    {p : Fin (arity (tags G needs)+G.size) → ZFCarrier (LStageZF β)}
    {v : Fin G.size → Ordinal.{u}} (hc : LabelCandidate G cut f pars p v) :
    (p (Fin.castAdd G.size (omegaIndex (tags G needs)))).val = Ordinal.omega0.toZFSet := by
  rw [hc.parameters]
  exact h.omega

theorem MetadataCorrect.at_zero {G : Diagram} {needs : List TopAtom}
    {cut : Nat} {f : Nat → Ordinal.{u}} {β : Ordinal.{u}}
    {pars : Fin (arity (tags G needs)) → ZFCarrier (LStageZF β)}
    (h : MetadataCorrect (tags G needs) pars)
    {p : Fin (arity (tags G needs)+G.size) → ZFCarrier (LStageZF β)}
    {v : Fin G.size → Ordinal.{u}} (hc : LabelCandidate G cut f pars p v) :
    (p (Fin.castAdd G.size (zeroIndex (tags G needs)))).val = ∅ := by
  rw [hc.parameters]
  exact h.zero

theorem MetadataCorrect.at_nat {G : Diagram} {needs : List TopAtom}
    {cut : Nat} {f : Nat → Ordinal.{u}} {β : Ordinal.{u}}
    {pars : Fin (arity (tags G needs)) → ZFCarrier (LStageZF β)}
    (h : MetadataCorrect (tags G needs) pars)
    {p : Fin (arity (tags G needs)+G.size) → ZFCarrier (LStageZF β)}
    {v : Fin G.size → Ordinal.{u}} (hc : LabelCandidate G cut f pars p v)
    (k : Nat) (hk : k ∈ tags G needs) :
    (p (Fin.castAdd G.size (natIndex (tags G needs) k))).val = natCode k := by
  rw [hc.parameters]
  exact h.nat k hk

end OneYTruth.ActualDiagramQueries

#print axioms OneYTruth.ActualDiagramQueries.metadata_correct
