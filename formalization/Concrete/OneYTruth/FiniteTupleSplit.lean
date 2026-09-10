import OneYTruth.FiniteWitnessReflection

/-! Keeping the initial variables literally fixed while reflecting all other
coordinates. The arity casts below do not add equations to the matrix. -/
namespace OneYTruth.FiniteLabelAssembly
open FirstOrder FirstOrder.Language
universe u v w

def splitIndex {n cut : Nat} (hc : cut ≤ n) (i : Fin n) : Fin (cut+(n-cut)) :=
  ⟨i.val,by omega⟩

def unsplitIndex {n cut : Nat} (hc : cut ≤ n) (i : Fin (cut+(n-cut))) : Fin n :=
  ⟨i.val,by omega⟩

@[simp] theorem unsplit_split {n cut : Nat} (hc : cut ≤ n) (i : Fin n) :
    unsplitIndex hc (splitIndex hc i) = i := rfl
@[simp] theorem split_unsplit {n cut : Nat} (hc : cut ≤ n) (i : Fin (cut+(n-cut))) :
    splitIndex hc (unsplitIndex hc i) = i := rfl

def prefixTuple {n cut : Nat} (hc : cut ≤ n) {A : Type v} (p : Fin n → A) : Fin cut → A :=
  fun i => p ⟨i.val,i.isLt.trans_le hc⟩

def suffixTuple {n cut : Nat} (hc : cut ≤ n) {A : Type v} (p : Fin n → A) : Fin (n-cut) → A :=
  fun i => p ⟨cut+i.val,by omega⟩

def joinTuple {n cut : Nat} (hc : cut ≤ n) {A : Type v}
    (p : Fin cut → A) (xs : Fin (n-cut) → A) : Fin n → A :=
  Fin.append p xs ∘ splitIndex hc

@[simp] theorem joinTuple_prefix {n cut : Nat} (hc : cut ≤ n) {A : Type v}
    (p : Fin cut → A) (xs : Fin (n-cut) → A) (i : Fin cut) :
    joinTuple hc p xs ⟨i.val,i.isLt.trans_le hc⟩ = p i := by
  change Fin.append p xs (Fin.castAdd (n-cut) i) = p i
  exact Fin.append_left p xs i

@[simp] theorem joinTuple_split {n cut : Nat} (hc : cut ≤ n) {A : Type v} (p : Fin n → A) :
    joinTuple hc (prefixTuple hc p) (suffixTuple hc p) = p := by
  funext i
  obtain ⟨j,hj⟩ : ∃ j, unsplitIndex hc j = i := ⟨splitIndex hc i,rfl⟩
  subst i
  induction j using Fin.addCases with
  | left j =>
      change Fin.append (prefixTuple hc p) (suffixTuple hc p) (Fin.castAdd (n-cut) j) = _
      rw [Fin.append_left]
      rfl
  | right j =>
      change Fin.append (prefixTuple hc p) (suffixTuple hc p) (Fin.natAdd cut j) = _
      rw [Fin.append_right]
      rfl

/-- A genuine Sigma-one map reflects exactly the suffix variables of a
single formula, preserving the pars by construction. -/
theorem reflect_tuple {k : Nat} {I : Type u} {A : Type v} {B : Type w}
    {M : Interpretation k I A} {N : Interpretation k I B} {f : A → B}
    (hf : ClosedSigmaOneMap M N f) {n cut : Nat} (hc : cut ≤ n)
    (φ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ)
    (pars : Fin cut → A) (ambient : Fin n → B)
    (hprefix : prefixTuple hc ambient = f ∘ pars)
    (hambient : realize N φ Empty.elim ambient) :
    ∃ q : Fin n → A, realize M φ Empty.elim q ∧ prefixTuple hc q = pars := by
  let ψ := renameScope (splitIndex hc) φ
  have hψ : IsSigmaOne ψ := hφ.renameScope (splitIndex hc)
  have hamb : ∃ xs : Fin (n-cut) → B,
      realize N ψ Empty.elim (Fin.append (f ∘ pars) xs) := by
    refine ⟨suffixTuple hc ambient,?_⟩
    rw [realize_renameScope]
    change realize N φ Empty.elim (joinTuple hc (f ∘ pars) (suffixTuple hc ambient))
    rw [← hprefix,joinTuple_split]
    exact hambient
  obtain ⟨xs,hxs⟩ := hf.reflect_finiteWitnesses ψ hψ pars hamb
  refine ⟨joinTuple hc pars xs,?_,?_⟩
  · exact (realize_renameScope M (splitIndex hc) φ (Fin.append pars xs)).mp hxs
  · funext i
    exact joinTuple_prefix hc pars xs i

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.reflect_tuple


