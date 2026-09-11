/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections

/-!
# Cantor--Schroeder--Bernstein inside the constructible universe

The usual least-closed-subset proof is carried out with Full Separation in
`LCarrier`.  The resulting bijection is then built by the definable relation
graph construction, so its graph is an actual member of `L`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-! ## Formula semantics for the least closed subset -/

def InRange {A : Type u} (E : A -> A -> Prop)
    (graph domain x : A) : Prop :=
  exists y : A, E y domain /\ GraphValue E graph y x

def SBBase {A : Type u} (E : A -> A -> Prop)
    (g a b x : A) : Prop :=
  E x a /\ Not (InRange E g b x)

def SBStep {A : Type u} (E : A -> A -> Prop)
    (f g closed z : A) : Prop :=
  exists x : A, E x closed /\
    exists y : A, GraphValue E f x y /\ GraphValue E g y z

def SBClosed {A : Type u} (E : A -> A -> Prop)
    (f g a b closed : A) : Prop :=
  IsSubsetOf E closed a /\
    (forall x : A, SBBase E g a b x -> E x closed) /\
      forall z : A, SBStep E f g closed z -> E z closed

def SBLeastMember {A : Type u} (E : A -> A -> Prop)
    (f g a b x : A) : Prop :=
  E x a /\ forall closed : A, SBClosed E f g a b closed -> E x closed

def SBGenerated {A : Type u} (E : A -> A -> Prop)
    (f g a b closed x : A) : Prop :=
  SBBase E g a b x \/ SBStep E f g closed x

def SBBijectionRel {A : Type u} (E : A -> A -> Prop)
    (f g a closed x y : A) : Prop :=
  (E x closed /\ GraphValue E f x y) \/
    (E x a /\ Not (E x closed) /\ GraphValue E g y x)

/-- `x` is in the range of `graph` restricted to `domain`. -/
def inRangeAt {n : Nat} (graph domain x : Fin n) : FOFormula n :=
  FOFormula.boundedEx domain
    (graphValueAt graph.castSucc (Fin.last n) x.castSucc)

@[simp]
theorem satisfies_inRangeAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (graph domain x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (inRangeAt graph domain x) s <->
      InRange E (s graph) (s domain) (s x) := by
  simp only [inRangeAt, FOFormula.satisfies_boundedEx,
    satisfies_graphValueAt, snoc_last, snoc_castSucc, InRange]

/-- The points of `a` omitted by the range of `g : b -> a`. -/
def sbBaseAt {n : Nat} (g a b x : Fin n) : FOFormula n :=
  .conj (.mem x a) (.neg (inRangeAt g b x))

@[simp]
theorem satisfies_sbBaseAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (g a b x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbBaseAt g a b x) s <->
      SBBase E (s g) (s a) (s b) (s x) := by
  simp only [sbBaseAt, FOFormula.Satisfies, satisfies_inRangeAt, SBBase]

/-- One application of `g o f` starting in `closed`. -/
def sbStepAt {n : Nat} (f g closed z : Fin n) : FOFormula n :=
  FOFormula.boundedEx closed
    (.ex (.conj
      (graphValueAt f.castSucc.castSucc
        (Fin.last n).castSucc (Fin.last (n + 1)))
      (graphValueAt g.castSucc.castSucc
        (Fin.last (n + 1)) z.castSucc.castSucc)))

@[simp]
theorem satisfies_sbStepAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g closed z : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbStepAt f g closed z) s <->
      SBStep E (s f) (s g) (s closed) (s z) := by
  simp only [sbStepAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, SBStep]

/-- A subset of `a` containing the base and closed under `g o f`. -/
def sbClosedAt {n : Nat}
    (f g a b closed : Fin n) : FOFormula n :=
  .conj (subsetAt closed a)
    (.conj
      (.all (.imp
        (sbBaseAt g.castSucc a.castSucc b.castSucc (Fin.last n))
        (.mem (Fin.last n) closed.castSucc)))
      (.all (.imp
        (sbStepAt f.castSucc g.castSucc closed.castSucc (Fin.last n))
        (.mem (Fin.last n) closed.castSucc))))

@[simp]
theorem satisfies_sbClosedAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b closed : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbClosedAt f g a b closed) s <->
      SBClosed E (s f) (s g) (s a) (s b) (s closed) := by
  simp only [sbClosedAt, FOFormula.Satisfies, satisfies_subsetAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_sbBaseAt, satisfies_sbStepAt,
    snoc_last, snoc_castSucc, SBClosed]

/-- Membership in the intersection of all closed subsets of `a`. -/
def sbLeastMemberAt {n : Nat} (f g a b x : Fin n) : FOFormula n :=
  .conj (.mem x a)
    (.all (.imp
      (sbClosedAt f.castSucc g.castSucc a.castSucc b.castSucc (Fin.last n))
      (.mem x.castSucc (Fin.last n))))

@[simp]
theorem satisfies_sbLeastMemberAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbLeastMemberAt f g a b x) s <->
      SBLeastMember E (s f) (s g) (s a) (s b) (s x) := by
  simp only [sbLeastMemberAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_sbClosedAt, snoc_last, snoc_castSucc, SBLeastMember]

/-- The base together with one step from `closed`. -/
def sbGeneratedAt {n : Nat}
    (f g a b closed x : Fin n) : FOFormula n :=
  .disj (sbBaseAt g a b x) (sbStepAt f g closed x)

@[simp]
theorem satisfies_sbGeneratedAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b closed x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbGeneratedAt f g a b closed x) s <->
      SBGenerated E (s f) (s g) (s a) (s b) (s closed) (s x) := by
  simp only [sbGeneratedAt, FOFormula.satisfies_disj,
    satisfies_sbBaseAt, satisfies_sbStepAt, SBGenerated]

/-- The piecewise relation used in the CSB construction. -/
def sbBijectionAt {n : Nat}
    (f g a closed x y : Fin n) : FOFormula n :=
  .disj
    (.conj (.mem x closed) (graphValueAt f x y))
    (.conj (.mem x a)
      (.conj (.neg (.mem x closed)) (graphValueAt g y x)))

@[simp]
theorem satisfies_sbBijectionAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a closed x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbBijectionAt f g a closed x y) s <->
      SBBijectionRel E (s f) (s g) (s a) (s closed) (s x) (s y) := by
  simp only [sbBijectionAt, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_graphValueAt, SBBijectionRel]

/-! ## The least closed subset of the domain -/

private def sbLeastMemberPredicate : FOFormula 5 :=
  sbLeastMemberAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)

private theorem sbLeastMember_assignment
    (f g a b x : Constructible.Model.LCarrier.{u}) :
    snoc ![f, g, a, b] x = ![f, g, a, b, x] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbLeastMemberPredicate
    (f g a b x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbLeastMemberPredicate (snoc ![f, g, a, b] x) <->
      SBLeastMember Constructible.Model.lCarrierMem f g a b x := by
  rw [sbLeastMember_assignment]
  exact satisfies_sbLeastMemberAt
    Constructible.Model.lCarrierMem
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)
      ![f, g, a, b, x]

/-- Full Separation constructs the least subset of `a` which contains the
points outside the range of `g` and is closed under `g o f`. -/
theorem exists_leastSBClosed_lCarrier
    {f g a b : Constructible.Model.LCarrier.{u}}
    (_hf : IsInjection Constructible.Model.lCarrierMem f a b)
    (hg : IsInjection Constructible.Model.lCarrierMem g b a) :
    exists closed : Constructible.Model.LCarrier.{u},
      SBClosed Constructible.Model.lCarrierMem f g a b closed /\
        forall candidate : Constructible.Model.LCarrier.{u},
          SBClosed Constructible.Model.lCarrierMem f g a b candidate ->
            IsSubsetOf Constructible.Model.lCarrierMem closed candidate := by
  rcases Constructible.Model.exists_separationLCarrier
      sbLeastMemberPredicate ![f, g, a, b] a with
    ⟨closed, hclosed⟩
  have hclosed_iff : forall x : Constructible.Model.LCarrier.{u},
      x.1 ∈ closed.1 <->
        SBLeastMember Constructible.Model.lCarrierMem f g a b x := by
    intro x
    rw [hclosed x, satisfies_sbLeastMemberPredicate]
    simp only [SBLeastMember, and_iff_right_iff_imp]
    exact fun h => h.1
  have hsubset : IsSubsetOf Constructible.Model.lCarrierMem closed a := by
    intro x hx
    exact ((hclosed_iff x).mp hx).1
  have hbase : forall x : Constructible.Model.LCarrier.{u},
      SBBase Constructible.Model.lCarrierMem g a b x -> x.1 ∈ closed.1 := by
    intro x hx
    apply (hclosed_iff x).mpr
    refine ⟨hx.1, ?_⟩
    intro candidate hcandidate
    exact hcandidate.2.1 x hx
  have hstep : forall z : Constructible.Model.LCarrier.{u},
      SBStep Constructible.Model.lCarrierMem f g closed z ->
        z.1 ∈ closed.1 := by
    rintro z ⟨x, hxclosed, y, hfxy, hgyz⟩
    have hzA : z.1 ∈ a.1 :=
      (hg.1.graphValue_mem_lCarrier hgyz).2
    apply (hclosed_iff z).mpr
    refine ⟨hzA, ?_⟩
    intro candidate hcandidate
    apply hcandidate.2.2 z
    refine ⟨x, ?_, y, hfxy, hgyz⟩
    exact ((hclosed_iff x).mp hxclosed).2 candidate hcandidate
  refine ⟨closed, ⟨hsubset, hbase, hstep⟩, ?_⟩
  intro candidate hcandidate x hxclosed
  exact ((hclosed_iff x).mp hxclosed).2 candidate hcandidate

private def sbGeneratedPredicate : FOFormula 6 :=
  sbGeneratedAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

private theorem sbGenerated_assignment
    (f g a b closed x : Constructible.Model.LCarrier.{u}) :
    snoc ![f, g, a, b, closed] x = ![f, g, a, b, closed, x] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbGeneratedPredicate
    (f g a b closed x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbGeneratedPredicate (snoc ![f, g, a, b, closed] x) <->
      SBGenerated Constructible.Model.lCarrierMem f g a b closed x := by
  rw [sbGenerated_assignment]
  exact satisfies_sbGeneratedAt
    Constructible.Model.lCarrierMem
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)
      ![f, g, a, b, closed, x]

/-- The least closed set is exactly the base together with one image under
`g o f`.  A second Separation instance supplies the closed comparison set
needed for the minimality argument. -/
theorem mem_leastSBClosed_iff_generated_lCarrier
    {f g a b closed : Constructible.Model.LCarrier.{u}}
    (hg : IsInjection Constructible.Model.lCarrierMem g b a)
    (hclosed : SBClosed Constructible.Model.lCarrierMem f g a b closed)
    (hminimal : forall candidate : Constructible.Model.LCarrier.{u},
      SBClosed Constructible.Model.lCarrierMem f g a b candidate ->
        IsSubsetOf Constructible.Model.lCarrierMem closed candidate)
    (x : Constructible.Model.LCarrier.{u}) :
    x.1 ∈ closed.1 <->
      SBGenerated Constructible.Model.lCarrierMem f g a b closed x := by
  rcases Constructible.Model.exists_separationLCarrier
      sbGeneratedPredicate ![f, g, a, b, closed] a with
    ⟨generated, hgenerated⟩
  have hgenerated_iff : forall z : Constructible.Model.LCarrier.{u},
      z.1 ∈ generated.1 <->
        z.1 ∈ a.1 /\
          SBGenerated Constructible.Model.lCarrierMem
            f g a b closed z := by
    intro z
    rw [hgenerated z, satisfies_sbGeneratedPredicate]
  have hgenerated_subset_closed :
      IsSubsetOf Constructible.Model.lCarrierMem generated closed := by
    intro z hz
    rcases (hgenerated_iff z).mp hz with ⟨_hzA, hzbase | hzstep⟩
    · exact hclosed.2.1 z hzbase
    · exact hclosed.2.2 z hzstep
  have hgenerated_closed :
      SBClosed Constructible.Model.lCarrierMem f g a b generated := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact ((hgenerated_iff z).mp hz).1
    · intro z hzbase
      apply (hgenerated_iff z).mpr
      exact ⟨hzbase.1, Or.inl hzbase⟩
    · rintro z ⟨w, hwgenerated, y, hfwy, hgyz⟩
      have hzA : z.1 ∈ a.1 :=
        (hg.1.graphValue_mem_lCarrier hgyz).2
      apply (hgenerated_iff z).mpr
      refine ⟨hzA, Or.inr ?_⟩
      exact ⟨w, hgenerated_subset_closed w hwgenerated,
        y, hfwy, hgyz⟩
  constructor
  · intro hxclosed
    have hxgenerated := hminimal generated hgenerated_closed x hxclosed
    exact ((hgenerated_iff x).mp hxgenerated).2
  · intro hxgenerated
    rcases hxgenerated with hxbase | hxstep
    · exact hclosed.2.1 x hxbase
    · exact hclosed.2.2 x hxstep

/-! ## The internally represented CSB bijection -/

private def sbBijectionPredicate : FOFormula 6 :=
  sbBijectionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

private theorem sbBijection_assignment
    (f g a closed x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![f, g, a, closed] x) y =
      ![f, g, a, closed, x, y] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbBijectionPredicate
    (f g a closed x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbBijectionPredicate (snoc (snoc ![f, g, a, closed] x) y) <->
      SBBijectionRel Constructible.Model.lCarrierMem
        f g a closed x y := by
  rw [sbBijection_assignment]
  exact satisfies_sbBijectionAt
    Constructible.Model.lCarrierMem
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)
      ![f, g, a, closed, x, y]

/-- The piecewise CSB relation has an actual constructible graph. -/
theorem exists_sbBijectionGraph_lCarrier
    {f g a b closed : Constructible.Model.LCarrier.{u}}
    (hf : IsInjection Constructible.Model.lCarrierMem f a b)
    (hg : IsInjection Constructible.Model.lCarrierMem g b a) :
    exists graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph a b /\
        forall x y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y <->
            SBBijectionRel Constructible.Model.lCarrierMem
              f g a closed x y := by
  let container := unionLCarrier a b
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      sbBijectionPredicate ![f, g, a, closed] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y <->
        SBBijectionRel Constructible.Model.lCarrierMem
          f g a closed x y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hxContainer, _hyContainer, hformula⟩
      exact (satisfies_sbBijectionPredicate f g a closed x y).mp hformula
    · intro hpiece
      have hxy : x.1 ∈ a.1 /\ y.1 ∈ b.1 := by
        rcases hpiece with hleft | hright
        · exact hf.1.graphValue_mem_lCarrier hleft.2
        · have hmem := hg.1.graphValue_mem_lCarrier hright.2.2
          exact ⟨hright.1, hmem.1⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff a b x).mpr (Or.inl hxy.1)
      · exact (mem_unionLCarrier_iff a b y).mpr (Or.inr hxy.2)
      · exact (satisfies_sbBijectionPredicate f g a closed x y).mpr
          hpiece
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  have hpiece :=
    (satisfies_sbBijectionPredicate f g a closed x y).mp hformula
  have hxy : x.1 ∈ a.1 /\ y.1 ∈ b.1 := by
    rcases hpiece with hleft | hright
    · exact hf.1.graphValue_mem_lCarrier hleft.2
    · have hmem := hg.1.graphValue_mem_lCarrier hright.2.2
      exact ⟨hright.1, hmem.1⟩
  exact ⟨x, hxy.1, y, hxy.2,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

/-- Cantor--Schroeder--Bernstein for internally represented injections.

Both input injections and the resulting bijection are graphs belonging to
`L`; no ambient equivalence is used as a graph witness. -/
theorem injects_antisymm_lCarrier
    {a b : Constructible.Model.LCarrier.{u}} :
    Injects Constructible.Model.lCarrierMem a b ->
      Injects Constructible.Model.lCarrierMem b a ->
        Equinumerous Constructible.Model.lCarrierMem a b := by
  classical
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  rcases exists_leastSBClosed_lCarrier hf hg with
    ⟨closed, hclosed, hminimal⟩
  have hfixed : forall x : Constructible.Model.LCarrier.{u},
      x.1 ∈ closed.1 <->
        SBGenerated Constructible.Model.lCarrierMem
          f g a b closed x :=
    mem_leastSBClosed_iff_generated_lCarrier hg hclosed hminimal
  rcases exists_sbBijectionGraph_lCarrier
      (closed := closed) hf hg with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hxA
    by_cases hxClosed : x.1 ∈ closed.1
    · rcases hf.2.1 x hxA with ⟨y, hyB, hfxy, hyUnique⟩
      refine ⟨y, hyB, (hvalue x y).mpr (Or.inl ⟨hxClosed, hfxy⟩), ?_⟩
      intro z hzB hxz
      rcases (hvalue x z).mp hxz with hleft | hright
      · exact hyUnique z hzB hleft.2
      · exact False.elim (hright.2.1 hxClosed)
    · have hxRange : InRange Constructible.Model.lCarrierMem g b x := by
        by_contra hxNotRange
        exact hxClosed (hclosed.2.1 x ⟨hxA, hxNotRange⟩)
      rcases hxRange with ⟨y, hyB, hgyx⟩
      refine ⟨y, hyB,
        (hvalue x y).mpr (Or.inr ⟨hxA, hxClosed, hgyx⟩), ?_⟩
      intro z hzB hxz
      rcases (hvalue x z).mp hxz with hleft | hright
      · exact False.elim (hxClosed hleft.1)
      · exact hg.2.2 x hxA y hyB hgyx z hzB hright.2.2
  · intro y hyB
    rcases hg.2.1 y hyB with ⟨x, hxA, hgyx, hxUnique⟩
    by_cases hxClosed : x.1 ∈ closed.1
    · have hxGenerated := (hfixed x).mp hxClosed
      rcases hxGenerated with hxBase | hxStep
      · exact False.elim (hxBase.2 ⟨y, hyB, hgyx⟩)
      · rcases hxStep with ⟨z, hzClosed, w, hfzw, hgwx⟩
        have hzA := hclosed.1 z hzClosed
        have hwB := (hf.1.graphValue_mem_lCarrier hfzw).2
        have hwy : w = y :=
          (hg.2.2 x hxA w hwB hgwx y hyB hgyx).symm
        have hfzy : GraphValue Constructible.Model.lCarrierMem f z y := by
          simpa only [hwy] using hfzw
        refine ⟨z, hzA,
          (hvalue z y).mpr (Or.inl ⟨hzClosed, hfzy⟩), ?_⟩
        intro q hqA hqy
        rcases (hvalue q y).mp hqy with hleft | hright
        · exact hf.2.2 y hyB z hzA hfzy q hqA hleft.2
        · have hqx := hxUnique q hqA hright.2.2
          subst q
          exact False.elim (hright.2.1 hxClosed)
    · refine ⟨x, hxA,
        (hvalue x y).mpr (Or.inr ⟨hxA, hxClosed, hgyx⟩), ?_⟩
      intro z hzA hzy
      rcases (hvalue z y).mp hzy with hleft | hright
      · have hxNow : x.1 ∈ closed.1 := hclosed.2.2 x
          ⟨z, hleft.1, y, hleft.2, hgyx⟩
        exact False.elim (hxClosed hxNow)
      · exact hxUnique z hzA hright.2.2

end Constructible.ContinuumFormula
