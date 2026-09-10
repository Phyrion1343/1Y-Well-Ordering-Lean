import OneYTruth.AuxiliaryRelationCode
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Separation

/-!
# Relativizing the finite auxiliary language to constructible set parameters

Every quantifier is restricted to the displayed domain U. The one extra
predicate is expanded to the literal set-membership code in W. Thus the
output is a genuine pure membership formula over L with two parameters.
-/

namespace OneYTruth.AuxiliaryCode

open Constructible Constructible.Model FirstOrder FirstOrder.Language

universe u

def termIndex {n : Nat} : Auxiliary.language.Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => nomatch e
  | .var (.inr i) => i
  | .func e _ => nomatch e

theorem realize_termIndex {A : Type*} (M : Auxiliary.Interpretation A) {n : Nat}
    (t : Auxiliary.language.Term (Empty ⊕ Fin n)) (xs : Fin n → A) :
    @Term.realize Auxiliary.language A M.structure _ (Sum.elim Empty.elim xs) t =
      xs (termIndex t) := by
  cases t with
  | var i => cases i with
    | inl e => nomatch e
    | inr => rfl
  | func e => nomatch e

def atomMap {n : Nat} (is : Fin 4 → Fin n) : Fin 5 → (Fin 2 ⊕ Fin n) :=
  Fin.cases (.inl 1) (fun i => .inr (is i))

def truthAtom {n : Nat} (is : Fin 4 → Fin n) :
    Language.setTheory.BoundedFormula (Fin 2) n :=
  BoundedFormula.relabel (Sum.elim Empty.elim (atomMap is))
    (toBoundedFormula relationFormula).toFormula

theorem realize_truthAtom {n : Nat} (is : Fin 4 → Fin n)
    (params : Fin 2 → LCarrier.{u}) (xs : Fin n → LCarrier.{u}) :
    (truthAtom is).Realize params xs ↔
      ZFSet.pair (ZFSet.pair (xs (is 0)).val (xs (is 1)).val)
        (ZFSet.pair (xs (is 2)).val (xs (is 3)).val) ∈ (params 1).val := by
  rw [truthAtom, BoundedFormula.realize_relabel]
  have hv : Sum.elim params (xs ∘ Fin.castAdd 0) ∘ Sum.elim Empty.elim (atomMap is) =
      Sum.elim Empty.elim (fun j => Sum.elim params xs (atomMap is j)) := by
    funext i
    cases i with
    | inl e => nomatch e
    | inr j => rfl
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [lCarrier_realize_toBoundedFormula, satisfies_relationFormula]
  rfl

/-- Free variables 0 and 1 name U and W; the source scope is retained. -/
def translate : {n : Nat} → Auxiliary.language.BoundedFormula Empty n →
    Language.setTheory.BoundedFormula (Fin 2) n
  | _, .falsum => .falsum
  | _, .equal t s => .equal (.var (.inr (termIndex t))) (.var (.inr (termIndex s)))
  | _, .rel .mem ts =>
      .rel .mem ![.var (.inr (termIndex (ts 0))), .var (.inr (termIndex (ts 1)))]
  | _, .rel .truth ts => truthAtom (fun i => termIndex (ts i))
  | _, .imp φ ψ => .imp (translate φ) (translate ψ)
  | n, .all φ => .all (.imp
      (.rel .mem ![.var (.inr (Fin.last n)), .var (.inl 0)]) (translate φ))

def interpretation (U W : ZFSet.{u}) : Auxiliary.Interpretation (ZFCarrier U) where
  mem a b := a.val ∈ b.val
  truth b ξ e a := ZFSet.pair (ZFSet.pair b.val ξ.val) (ZFSet.pair e.val a.val) ∈ W

def intoL (U : LCarrier.{u}) (x : ZFCarrier U.val) : LCarrier.{u} :=
  ⟨x.val, mem_L_of_mem x.property U.property⟩

theorem intoL_snoc (U : LCarrier.{u}) {n : Nat} (xs : Fin n → ZFCarrier U.val)
    (x : ZFCarrier U.val) :
    (fun i => intoL U ((Fin.snoc xs x : Fin (n + 1) → ZFCarrier U.val) i)) =
      Fin.snoc (fun i => intoL U (xs i)) (intoL U x) :=
  Fin.comp_snoc (intoL U) xs x

theorem realize_translate (U W : LCarrier.{u}) {n : Nat}
    (φ : Auxiliary.language.BoundedFormula Empty n) (xs : Fin n → ZFCarrier U.val) :
    (translate φ).Realize ![U, W] (fun i => intoL U (xs i)) ↔
      Auxiliary.realize (interpretation U.val W.val) φ Empty.elim xs := by
  classical
  induction φ with
  | falsum => rfl
  | equal t s =>
      change intoL U (xs (termIndex t)) = intoL U (xs (termIndex s)) ↔
        @Term.realize _ _ (interpretation U.val W.val).structure _ (Sum.elim Empty.elim xs) t =
          @Term.realize _ _ (interpretation U.val W.val).structure _ (Sum.elim Empty.elim xs) s
      rw [realize_termIndex, realize_termIndex]
      exact ⟨fun h => Subtype.ext (congrArg (fun z : LCarrier.{u} => z.val) h),
        congrArg (intoL U)⟩
  | rel r ts =>
      cases r with
      | mem =>
          change (xs (termIndex (ts 0))).val ∈ (xs (termIndex (ts 1))).val ↔ _
          simp only [Auxiliary.realize, BoundedFormula.Realize,
            realize_termIndex]
          rfl
      | truth =>
          rw [translate, realize_truthAtom]
          simp only [Auxiliary.realize, BoundedFormula.Realize,
            realize_termIndex, intoL,
            Matrix.cons_val_one, Matrix.cons_val_zero]
          rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ xs) (ihψ xs)
  | @all n φ ih =>
      simp only [translate, Auxiliary.realize, BoundedFormula.Realize,
        setTheoryStructure_relMap,
        Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize,
        Sum.elim_inr, Sum.elim_inl, Fin.snoc_last, lCarrierMem]
      change (∀ z : LCarrier.{u}, z.val ∈ U.val →
        (translate φ).Realize ![U, W] (Fin.snoc (fun i => intoL U (xs i)) z)) ↔
          ∀ x : ZFCarrier U.val, Auxiliary.realize (interpretation U.val W.val)
            φ Empty.elim (Fin.snoc xs x)
      constructor
      · intro h x
        apply (ih (Fin.snoc xs x)).mp
        rw [intoL_snoc]
        exact h (intoL U x) x.property
      · intro h z hz
        let x : ZFCarrier U.val := ⟨z.val, hz⟩
        have hφ := (ih (Fin.snoc xs x)).mpr (h x)
        rw [intoL_snoc] at hφ
        have hx : intoL U x = z := Subtype.ext rfl
        simpa only [hx] using hφ

end OneYTruth.AuxiliaryCode
