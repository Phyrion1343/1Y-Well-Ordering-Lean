import OneYTruth.OrdinalTupleCertificate
import OneYTruth.RootSemantics
import OneY.RootIndexed.Representation

/-! # Decoding finite reflected labels into an actual root-indexed representation

These are finite combination theorems, not the finite-reflection theorem.
All candidate ordinal, domain, and relation facts are explicit. Top demands
refer to the ambient ordinal externally; its code is never presumed to be
an element of its own constructible level.
-/

namespace OneYTruth.FiniteLabelAssembly

open Constructible Constructible.Model OneY.RootIndexed

universe u

def CodeDomain (D : Ordinal.{u} → Prop) (z : ZFSet.{u}) : Prop :=
  ∃ a : Ordinal.{u}, a.toZFSet = z ∧ D a

def CodeRelation (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (k : Nat) (zη za zb : ZFSet.{u}) : Prop :=
  ∃ η a b : Ordinal.{u}, η.toZFSet = zη ∧ a.toZFSet = za ∧ b.toZFSet = zb ∧ R k η a b

def CodeTopRelation (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (top : Ordinal.{u}) (k : Nat) (zη za : ZFSet.{u}) : Prop :=
  ∃ η a : Ordinal.{u}, η.toZFSet = zη ∧ a.toZFSet = za ∧ R k η a top

theorem codeDomain_codes (D : Ordinal.{u} → Prop) (a : Ordinal.{u}) :
    CodeDomain D a.toZFSet ↔ D a := by
  constructor
  · rintro ⟨b,hb,hD⟩
    exact Ordinal.toZFSet_injective hb ▸ hD
  · exact fun h => ⟨a,rfl,h⟩

theorem codeRelation_codes (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (k : Nat) (η a b : Ordinal.{u}) :
    CodeRelation R k η.toZFSet a.toZFSet b.toZFSet ↔ R k η a b := by
  constructor
  · rintro ⟨η',a',b',hη,ha,hb,h⟩
    simpa only [Ordinal.toZFSet_injective hη,Ordinal.toZFSet_injective ha,
      Ordinal.toZFSet_injective hb] using h
  · exact fun h => ⟨η,a,b,rfl,rfl,rfl,h⟩

theorem codeTopRelation_codes (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (top : Ordinal.{u}) (k : Nat) (η a : Ordinal.{u}) :
    CodeTopRelation R top k η.toZFSet a.toZFSet ↔ R k η a top := by
  constructor
  · rintro ⟨η',a',hη,ha,h⟩
    simpa only [Ordinal.toZFSet_injective hη,Ordinal.toZFSet_injective ha] using h
  · exact fun h => ⟨η,a,rfl,rfl,h⟩

noncomputable def extend {n : Nat} (v : Fin n → Ordinal.{u}) (i : Nat) : Ordinal.{u} :=
  if hi : i < n then v ⟨i,hi⟩ else 0

theorem extend_at {n : Nat} (v : Fin n → Ordinal.{u}) (i : Fin n) : extend v i.val = v i := by
  simp only [extend,dif_pos i.isLt]

def AtomFinHolds (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (v : Fin n → Ordinal.{u}) (e : Atom) (he : e.Valid n) : Prop :=
  R e.layer (v ⟨e.root,by rcases he with ⟨_,_,_⟩; omega⟩)
    (v ⟨e.parent,by rcases he with ⟨_,_,_⟩; omega⟩) (v ⟨e.child,he.2.2⟩)

def NeedFinHolds (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (v : Fin n → Ordinal.{u}) (top : Ordinal.{u})
    (d : TopAtom) (hd : d.Valid n) : Prop :=
  R d.layer (v ⟨d.root,by rcases hd with ⟨_,_⟩; omega⟩) (v ⟨d.parent,hd.2⟩) top

theorem representation_of_finite (D : Ordinal.{u} → Prop)
    (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (v : Fin G.size → Ordinal.{u})
    (hD : ∀ i, D (v i)) (hmono : StrictMono v)
    (hR : ∀ e, ∀ he : e ∈ G.atoms, AtomFinHolds R v e (G.valid e he)) :
    Representation (· < ·) D R G (extend v) := by
  constructor
  · intro i hi
    rw [extend_at v ⟨i,hi⟩]
    exact hD ⟨i,hi⟩
  · intro i j hij hj
    rw [extend_at v ⟨i,hij.trans hj⟩,extend_at v ⟨j,hj⟩]
    exact hmono hij
  · intro e he
    have hv := G.valid e he
    have hp : e.parent < G.size := hv.2.1.trans hv.2.2
    have hr : e.root < G.size := hv.1.trans_lt hp
    change R e.layer (extend v e.root) (extend v e.parent) (extend v e.child)
    rw [extend_at v ⟨e.root,hr⟩,extend_at v ⟨e.parent,hp⟩,extend_at v ⟨e.child,hv.2.2⟩]
    exact hR e he

theorem bounded_of_finite {n : Nat} (v : Fin n → Ordinal.{u}) (top : Ordinal.{u})
    (h : ∀ i, v i < top) : Bounded (· < ·) n (extend v) top := by
  intro i hi
  rw [extend_at v ⟨i,hi⟩]
  exact h ⟨i,hi⟩

theorem needs_of_finite (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (v : Fin n → Ordinal.{u}) (top : Ordinal.{u}) (needs : List TopAtom)
    (hvalid : ∀ d ∈ needs, d.Valid n)
    (h : ∀ d, ∀ hd : d ∈ needs, NeedFinHolds R v top d (hvalid d hd)) :
    ∀ d ∈ needs, d.Holds R (extend v) top := by
  intro d hd
  have hv := hvalid d hd
  have hr : d.root < n := hv.1.trans_lt hv.2
  change R d.layer (extend v d.root) (extend v d.parent) top
  rw [extend_at v ⟨d.root,hr⟩,extend_at v ⟨d.parent,hv.2⟩]
  exact h d hd

theorem fixed_of_finite {n cut : Nat} (hcut : cut ≤ n) (v : Fin n → Ordinal.{u})
    (f : Nat → Ordinal.{u})
    (h : ∀ i : Fin n, i.val < cut → (v i).toZFSet = (f i.val).toZFSet) :
    ∀ i, i < cut → extend v i = f i := by
  intro i hi
  rw [extend_at v ⟨i,hi.trans_le hcut⟩]
  exact Ordinal.toZFSet_injective (h ⟨i,hi.trans_le hcut⟩ hi)

end OneYTruth.FiniteLabelAssembly

#print axioms OneYTruth.FiniteLabelAssembly.representation_of_finite

