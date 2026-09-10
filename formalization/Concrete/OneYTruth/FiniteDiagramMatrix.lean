import OneYTruth.FiniteSigmaChecks
import OneYTruth.FiniteTupleDecoding

/-! The finite diagram matrix is assembled from its individual queries.
The local queries are explicit syntax with genuine Sigma-one proofs. Their
actual Adequate/R instantiations are a separate semantic obligation. -/
namespace OneYTruth.FiniteLabelAssembly
open Constructible FirstOrder FirstOrder.Language OneY.RootIndexed
universe u v w

structure QueryFamily (K : Nat) (J : Type u) (G : Diagram) (needs : List TopAtom) (scope : Nat) where
  domain : Fin G.size → (language K J).BoundedFormula Empty scope
  atom : Atom → (language K J).BoundedFormula Empty scope
  need : TopAtom → (language K J).BoundedFormula Empty scope
  domain_sigma : ∀ i, IsSigmaOne (domain i)
  atom_sigma : ∀ e ∈ G.atoms, IsSigmaOne (atom e)
  need_sigma : ∀ d ∈ needs, IsSigmaOne (need d)

private theorem all_append {A : Type v} {m n : Nat} (P : A → Prop)
    (f : Fin m → A) (g : Fin n → A) :
    (∀ i, P (Fin.append f g i)) ↔ (∀ i, P (f i)) ∧ ∀ j, P (g j) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd n i),
      fun j => by simpa using h (Fin.natAdd m j)⟩
  · rintro ⟨hf,hg⟩ i
    induction i using Fin.addCases with
    | left i => simpa using hf i
    | right i => simpa using hg i

private theorem all_cons {A : Type v} {n : Nat} (P : A → Prop)
    (a : A) (f : Fin n → A) :
    (∀ i, P ((show Fin (n+1) → A from Fin.cons a f) i)) ↔ P a ∧ ∀ i, P (f i) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0,fun i => by simpa using h i.succ⟩
  · rintro ⟨ha,hf⟩ i
    induction i using Fin.cases with
    | zero => simpa using ha
    | succ i => simpa using hf i

private theorem all_get {A : Type v} (l : List A) (P : A → Prop) :
    (∀ i, P (l.get i)) ↔ ∀ a ∈ l, P a := by
  constructor
  · intro h a ha
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
    exact hi ▸ h i
  · intro h i
    exact h _ (List.get_mem l i)

variable {K : Nat} {J : Type u} {G : Diagram} {needs : List TopAtom} {scope : Nat}

def diagramChecks (slots : Fin (G.size+1) → Fin scope)
    (Q : QueryFamily K J G needs scope) :
    Fin (G.size+(G.atoms.length+needs.length)+1) → (language K J).BoundedFormula Empty scope :=
  Fin.cons (renameScope slots (OrdinalTupleCertificate.mixedFormula K J G.size))
    (Fin.append Q.domain (Fin.append (fun i => Q.atom (G.atoms.get i))
      (fun i => Q.need (needs.get i))))

theorem diagramChecks_sigma (slots : Fin (G.size+1) → Fin scope)
    (Q : QueryFamily K J G needs scope) : ∀ i, IsSigmaOne (diagramChecks slots Q i) := by
  rw [diagramChecks,all_cons,all_append,all_append]
  exact ⟨.deltaZero ((OrdinalTupleCertificate.mixedFormula_isDeltaZero K J G.size).renameScope slots),
    Q.domain_sigma,(fun i => Q.atom_sigma _ (List.get_mem _ i)),
    (fun i => Q.need_sigma _ (List.get_mem _ i))⟩

noncomputable def diagramFormula (slots : Fin (G.size+1) → Fin scope)
    (Q : QueryFamily K J G needs scope) : (language K J).BoundedFormula Empty scope :=
  FiniteSigmaChecks.formula.{u,v} (diagramChecks slots Q) (diagramChecks_sigma slots Q)

theorem diagramFormula_sigma (slots : Fin (G.size+1) → Fin scope)
    (Q : QueryFamily K J G needs scope) : IsSigmaOne (diagramFormula.{u,v} slots Q) :=
  FiniteSigmaChecks.formula_isSigmaOne _ _

theorem realize_diagramFormula (slots : Fin (G.size+1) → Fin scope)
    (Q : QueryFamily K J G needs scope) {A : Type v} (N : Interpretation K J A)
    (p : Fin scope → A) :
    realize N (diagramFormula.{u,v} slots Q) Empty.elim p ↔
      realize N (OrdinalTupleCertificate.mixedFormula K J G.size) Empty.elim (p ∘ slots) ∧
      (∀ i, realize N (Q.domain i) Empty.elim p) ∧
      (∀ e ∈ G.atoms, realize N (Q.atom e) Empty.elim p) ∧
      (∀ d ∈ needs, realize N (Q.need d) Empty.elim p) := by
  rw [diagramFormula,FiniteSigmaChecks.realize_formula,diagramChecks]
  rw [all_cons (fun φ => realize N φ Empty.elim p),
    all_append (fun φ => realize N φ Empty.elim p),
    all_append (fun φ => realize N φ Empty.elim p),
    all_get G.atoms (fun e => realize N (Q.atom e) Empty.elim p),
    all_get needs (fun d => realize N (Q.need d) Empty.elim p),realize_renameScope]

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.realize_diagramFormula



