import OneYTruth.Language
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceZF

/-!
# Genuine set codes for mixed-language formulas

The independent raw tree retains the named index as data. Scope checking
recovers Mathlib formulas; the set encoder uses finite sequences of genuine
`ZFSet`s. No uniform satisfaction predicate or internal recursion certificate
is assumed by this syntax coding layer.
-/

namespace OneYTruth.FormulaCode

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF

universe u v w

inductive Raw (I : Type u) : Type u
  | falsum
  | equal (i j : Nat)
  | mem (i j : Nat)
  | diagonal (block index formula assignment : Nat)
  | named (index : I) (formula assignment : Nat)
  | imp (left right : Raw I)
  | all (body : Raw I)
  deriving DecidableEq

/-- With no free variables, every term is precisely one scoped variable. -/
def termIndex {k : Nat} {I : Type u} {n : Nat} :
    (OneYTruth.language k I).Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => nomatch e
  | .var (.inr i) => i
  | .func e _ => nomatch e

@[simp]
theorem var_termIndex {k : Nat} {I : Type u} {n : Nat}
    (t : (OneYTruth.language k I).Term (Empty ⊕ Fin n)) :
    Term.var (Sum.inr (termIndex t)) = t := by
  cases t with
  | var a => cases a with
    | inl e => nomatch e
    | inr => rfl
  | func e => nomatch e

def toRaw {k : Nat} {I : Type u} : {n : Nat} →
    (OneYTruth.language k I).BoundedFormula Empty n → Raw I
  | _, .falsum => .falsum
  | _, .equal t s => .equal (termIndex t).val (termIndex s).val
  | _, .rel (.mem) ts => .mem (termIndex (ts 0)).val (termIndex (ts 1)).val
  | _, .rel (.diagonal j) ts => .diagonal j.val (termIndex (ts 0)).val
      (termIndex (ts 1)).val (termIndex (ts 2)).val
  | _, .rel (.named i) ts => .named i (termIndex (ts 0)).val (termIndex (ts 1)).val
  | _, .imp φ ψ => .imp (toRaw φ) (toRaw ψ)
  | _, .all φ => .all (toRaw φ)

def finOfNat (n i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

@[simp]
theorem finOfNat_val {n : Nat} (i : Fin n) : finOfNat n i.val = some i := by
  simp [finOfNat, i.isLt]

def ofRaw {I : Type u} (k : Nat) : (n : Nat) → Raw I →
    Option ((OneYTruth.language k I).BoundedFormula Empty n)
  | _, .falsum => some .falsum
  | n, .equal i j => match finOfNat n i, finOfNat n j with
      | some i, some j => some (.equal (.var (.inr i)) (.var (.inr j)))
      | _, _ => none
  | n, .mem i j => match finOfNat n i, finOfNat n j with
      | some i, some j => some (.rel .mem ![.var (.inr i), .var (.inr j)])
      | _, _ => none
  | n, .diagonal j i e s => match finOfNat k j, finOfNat n i, finOfNat n e, finOfNat n s with
      | some j, some i, some e, some s =>
        some (.rel (.diagonal j) ![.var (.inr i), .var (.inr e), .var (.inr s)])
      | _, _, _, _ => none
  | n, .named i e s => match finOfNat n e, finOfNat n s with
      | some e, some s => some (.rel (.named i) ![.var (.inr e), .var (.inr s)])
      | _, _ => none
  | n, .imp φ ψ => do
      let φ ← ofRaw k n φ
      let ψ ← ofRaw k n ψ
      return .imp φ ψ
  | n, .all φ => return .all (← ofRaw k (n + 1) φ)

theorem tuple_two_eta {A : Type*} (v : Fin 2 → A) : ![v 0, v 1] = v := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

theorem tuple_three_eta {A : Type*} (v : Fin 3 → A) : ![v 0, v 1, v 2] = v := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun l => ?_) j
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  rfl

/-- Scope checking is a left inverse to erasing the intrinsic scopes. -/
theorem ofRaw_toRaw {k : Nat} {I : Type u} {n : Nat}
    (φ : (OneYTruth.language k I).BoundedFormula Empty n) :
    ofRaw k n (toRaw φ) = some φ := by
  induction φ with
  | falsum => rfl
  | equal t s => simp [toRaw, ofRaw]
  | rel r ts =>
    cases r <;> simp [toRaw, ofRaw, tuple_two_eta, tuple_three_eta]
  | imp φ ψ ihφ ihψ => simp [toRaw, ofRaw, ihφ, ihψ]
  | all φ ih => simp [toRaw, ofRaw, ih]

theorem toRaw_injective {k : Nat} {I : Type u} {n : Nat} :
    Function.Injective (toRaw : (OneYTruth.language k I).BoundedFormula Empty n → Raw I) := by
  intro φ ψ h
  have heq := congrArg (ofRaw k n) h
  simpa only [ofRaw_toRaw, Option.some.injEq] using heq

/-- The code includes a distinct finite constructor tag and each literal index. -/
noncomputable def rawCode {I : Type v} (indexCode : I → ZFSet.{u}) : Raw I → ZFSet.{u}
  | .falsum => sequenceCode [natCode 0]
  | .equal i j => sequenceCode [natCode 1, natCode i, natCode j]
  | .mem i j => sequenceCode [natCode 2, natCode i, natCode j]
  | .diagonal j i e s => sequenceCode [natCode 3, natCode j, natCode i, natCode e, natCode s]
  | .named i e s => sequenceCode [natCode 4, indexCode i, natCode e, natCode s]
  | .imp φ ψ => sequenceCode [natCode 5, rawCode indexCode φ, rawCode indexCode ψ]
  | .all φ => sequenceCode [natCode 6, rawCode indexCode φ]

theorem rawCode_injective {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : Function.Injective indexCode) : Function.Injective (rawCode indexCode) := by
  intro φ ψ h
  induction φ generalizing ψ with
  | falsum => cases ψ <;> simp_all [rawCode]
  | equal i j => cases ψ <;> simp_all [rawCode]
  | mem i j => cases ψ <;> simp_all [rawCode]
  | diagonal j i e s => cases ψ <;> simp_all [rawCode]
  | named i e s => cases ψ <;> simp_all [rawCode, hi.eq_iff]
  | imp φ χ ihφ ihχ =>
    cases ψ <;> simp [rawCode] at h
    exact congrArg₂ Raw.imp (ihφ h.1) (ihχ h.2)
  | all φ ih =>
    cases ψ <;> simp [rawCode] at h
    exact congrArg Raw.all (ih h)

/-- These codes are constructible whenever the literal named-index codes are. -/
theorem rawCode_mem_L {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ Constructible.L) (φ : Raw I) :
    rawCode indexCode φ ∈ Constructible.L := by
  induction φ <;> simp only [rawCode] <;> apply sequenceCode_mem_L <;>
    simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp, false_implies,
      forall_const, natCode_mem_L, and_true]

noncomputable def formulaCode {k : Nat} {I : Type v} {n : Nat}
    (indexCode : I → ZFSet.{u})
    (φ : (OneYTruth.language k I).BoundedFormula Empty n) : ZFSet.{u} :=
  rawCode indexCode (toRaw φ)

theorem formulaCode_injective {k : Nat} {I : Type v} {n : Nat}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode) :
    Function.Injective (formulaCode (k := k) (n := n) indexCode) :=
  (rawCode_injective hi).comp toRaw_injective

theorem formulaCode_mem_L {k : Nat} {I : Type v} {n : Nat}
    {indexCode : I → ZFSet.{u}} (hi : ∀ i, indexCode i ∈ Constructible.L)
    (φ : (OneYTruth.language k I).BoundedFormula Empty n) :
    formulaCode indexCode φ ∈ Constructible.L := rawCode_mem_L hi _

def Raw.map {I : Type v} {J : Type w} (f : I → J) : Raw I → Raw J
  | .falsum => .falsum
  | .equal i j => .equal i j
  | .mem i j => .mem i j
  | .diagonal j i e s => .diagonal j i e s
  | .named i e s => .named (f i) e s
  | .imp φ ψ => .imp (φ.map f) (ψ.map f)
  | .all φ => .all (φ.map f)

theorem rawCode_map {I : Type v} {J : Type w} (f : I → J)
    (cI : I → ZFSet.{u}) (cJ : J → ZFSet.{u}) (hc : ∀ i, cJ (f i) = cI i)
    (φ : Raw I) : rawCode cJ (φ.map f) = rawCode cI φ := by
  induction φ <;> simp_all [Raw.map, rawCode]

theorem termIndex_namedMap {k : Nat} {I : Type v} {J : Type w} {n : Nat}
    (f : I → J) (t : (OneYTruth.language k I).Term (Empty ⊕ Fin n)) :
    termIndex ((namedMap f).onTerm t) = termIndex t := by
  cases t with
  | var a => cases a with
    | inl e => nomatch e
    | inr => rfl
  | func e => nomatch e

theorem toRaw_namedMap {k : Nat} {I : Type v} {J : Type w} {n : Nat}
    (f : I → J) (φ : (OneYTruth.language k I).BoundedFormula Empty n) :
    toRaw ((namedMap f).onBoundedFormula φ) = (toRaw φ).map f := by
  induction φ with
  | falsum => rfl
  | equal t s => simp [toRaw, Raw.map, LHom.onBoundedFormula, termIndex_namedMap, Term.bdEqual]
  | rel r ts =>
    cases r with
    | mem =>
      change Raw.mem (termIndex ((namedMap f).onTerm (ts 0))).val
        (termIndex ((namedMap f).onTerm (ts 1))).val =
        Raw.mem (termIndex (ts 0)).val (termIndex (ts 1)).val
      rw [termIndex_namedMap, termIndex_namedMap]
    | diagonal j =>
      change Raw.diagonal j.val (termIndex ((namedMap f).onTerm (ts 0))).val
        (termIndex ((namedMap f).onTerm (ts 1))).val (termIndex ((namedMap f).onTerm (ts 2))).val =
        Raw.diagonal j.val (termIndex (ts 0)).val (termIndex (ts 1)).val (termIndex (ts 2)).val
      rw [termIndex_namedMap, termIndex_namedMap, termIndex_namedMap]
    | named i =>
      change Raw.named (f i) (termIndex ((namedMap f).onTerm (ts 0))).val
        (termIndex ((namedMap f).onTerm (ts 1))).val =
        Raw.named (f i) (termIndex (ts 0)).val (termIndex (ts 1)).val
      rw [termIndex_namedMap, termIndex_namedMap]
  | imp φ ψ ihφ ihψ => simp [LHom.onBoundedFormula, toRaw, Raw.map, ihφ, ihψ]
  | all φ ih => simp [LHom.onBoundedFormula, toRaw, Raw.map, ih]

/-- A formula's set code is unchanged when its names are included in a larger stage. -/
theorem formulaCode_namedMap {k : Nat} {I : Type v} {J : Type w} {n : Nat}
    (f : I → J) (cI : I → ZFSet.{u}) (cJ : J → ZFSet.{u})
    (hc : ∀ i, cJ (f i) = cI i)
    (φ : (OneYTruth.language k I).BoundedFormula Empty n) :
    formulaCode cJ ((namedMap f).onBoundedFormula φ) = formulaCode cI φ := by
  unfold formulaCode
  rw [toRaw_namedMap, rawCode_map f cI cJ hc]

/-- Packing includes the assignment arity, so different arities cannot collide. -/
abbrev Packed (k : Nat) (I : Type v) :=
  Σ n, (OneYTruth.language k I).BoundedFormula Empty n

noncomputable def packedCode {k : Nat} {I : Type v} (indexCode : I → ZFSet.{u})
    (φ : Packed k I) : ZFSet.{u} :=
  ZFSet.pair (natCode φ.1) (formulaCode indexCode φ.2)

theorem packedCode_injective {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : Function.Injective indexCode) : Function.Injective (packedCode (k := k) indexCode) := by
  rintro ⟨n, φ⟩ ⟨m, ψ⟩ h
  obtain ⟨hn, hφ⟩ := ZFSet.pair_inj.mp h
  have hnm : n = m := natCode_injective hn
  subst m
  have hφψ : φ = ψ := formulaCode_injective hi hφ
  subst ψ
  rfl

theorem packedCode_mem_L {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ Constructible.L) (φ : Packed k I) :
    packedCode indexCode φ ∈ Constructible.L :=
  orderedPair_mem_L (natCode_mem_L _) (formulaCode_mem_L hi _)

/-- In the intended application the named index is the ordinal itself. -/
noncomputable def ordinalIndexCode {η : Ordinal.{u}} (i : {ξ : Ordinal.{u} // ξ < η}) :
    ZFSet.{u} := i.val.toZFSet

theorem ordinalIndexCode_injective {η : Ordinal.{u}} :
    Function.Injective (ordinalIndexCode (η := η)) :=
  Ordinal.toZFSet_injective.comp Subtype.val_injective

theorem ordinalIndexCode_mem_L {η : Ordinal.{u}} (i : {ξ : Ordinal.{u} // ξ < η}) :
    ordinalIndexCode i ∈ Constructible.L := ordinal_toZFSet_mem_L i.val

end OneYTruth.FormulaCode
