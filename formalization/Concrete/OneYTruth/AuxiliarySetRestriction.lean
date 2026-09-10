import OneYTruth.AuxiliarySeparationSchema

/-! Actual set-domain restrictions of the auxiliary structure. -/

namespace OneYTruth.Auxiliary

open Constructible FirstOrder FirstOrder.Language

universe u v

def inclusion {U V : ZFSet.{u}} (h : V ⊆ U) (x : ZFCarrier V) : ZFCarrier U :=
  ⟨x.val, h x.property⟩

def restrict {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U)) (h : V ⊆ U) :
    Interpretation (ZFCarrier V) where
  mem a b := M.mem (inclusion h a) (inclusion h b)
  truth b ξ e a := M.truth (inclusion h b) (inclusion h ξ) (inclusion h e) (inclusion h a)

def setSubstructure {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U)) (V : ZFSet.{u}) :
    @language.Substructure (ZFCarrier U) M.structure := by
  letI := M.structure
  exact { carrier := {x | x.val ∈ V}, fun_mem := fun {_} e => nomatch e }

def restrictionEquiv {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U)) (h : V ⊆ U) :
    letI := (restrict M h).structure
    letI := (onSet M (setSubstructure M V : Set (ZFCarrier U))).structure
    ZFCarrier V ≃[language] (setSubstructure M V : Set (ZFCarrier U)) := by
  letI := (restrict M h).structure
  letI := (onSet M (setSubstructure M V : Set (ZFCarrier U))).structure
  exact {
    toFun := fun x => ⟨inclusion h x, x.property⟩
    invFun := fun x => ⟨x.val.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_fun' := fun {_} e => nomatch e
    map_rel' := fun {_} r xs => by cases r <;> rfl }

theorem realize_restrict {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (h : V ⊆ U) (he : letI := M.structure; (setSubstructure M V).IsElementary)
    {α : Type v} {n : Nat} (φ : language.BoundedFormula α n)
    (v : α → ZFCarrier V) (xs : Fin n → ZFCarrier V) :
    realize (restrict M h) φ v xs ↔
      realize M φ (fun i => inclusion h (v i)) (fun i => inclusion h (xs i)) := by
  letI := M.structure
  letI := (restrict M h).structure
  letI := (onSet M (setSubstructure M V : Set (ZFCarrier U))).structure
  let S : @language.ElementarySubstructure (ZFCarrier U) M.structure :=
    ⟨setSubstructure M V, he⟩
  let e := restrictionEquiv M h
  have heq := e.toElementaryEmbedding.map_boundedFormula φ v xs
  have hon := realize_onSet M S φ (fun i => e (v i)) (fun i => e (xs i))
  exact heq.symm.trans hon

theorem restrict_hasSeparation {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hmem : M.mem = zfCarrierMem U) (h : V ⊆ U)
    (he : letI := M.structure; (setSubstructure M V).IsElementary)
    (hSep : HasSeparation M) : HasSeparation (restrict M h) := by
  have hsmallmem : (restrict M h).mem = zfCarrierMem V := by
    funext x y
    exact congrFun (congrFun hmem (inclusion h x)) (inclusion h y)
  apply (hasRelSeparation_iff (restrict M h) hsmallmem).mp
  have hRel := (hasRelSeparation_iff M hmem).mpr hSep
  intro n φ xs a
  apply (realize_separationQuery (restrict M h) φ xs a).mp
  apply (realize_restrict M h he (separationQuery φ) Empty.elim (Fin.snoc xs a)).mpr
  have hv : (fun i => inclusion h (Empty.elim i : ZFCarrier V)) =
      (Empty.elim : Empty → ZFCarrier U) := by
    funext i
    nomatch i
  have hx : (fun i => inclusion h ((Fin.snoc xs a : Fin (n + 1) → ZFCarrier V) i)) =
      Fin.snoc (fun i => inclusion h (xs i)) (inclusion h a) := Fin.comp_snoc (inclusion h) xs a
  rw [hv, hx, realize_separationQuery]
  exact hRel n φ (fun i => inclusion h (xs i)) (inclusion h a)

theorem realize_restrict_reduct {U V : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (h : V ⊆ U) (he : letI := M.structure; (setSubstructure M V).IsElementary)
    {k : Nat} {I : Type v} {α : Type*} {n : Nat}
    (block : Fin (k + 1) → ZFCarrier V) (index : I → ZFCarrier V)
    (φ : (OneYTruth.language k I).BoundedFormula α n)
    (v : α → ZFCarrier V) (xs : Fin n → ZFCarrier V) :
    OneYTruth.realize (reduct (restrict M h) block index) φ v xs ↔
      OneYTruth.realize (reduct M (fun j => inclusion h (block j)) (fun i => inclusion h (index i)))
        φ (fun i => inclusion h (v i)) (fun i => inclusion h (xs i)) := by
  rw [← realize_translate (restrict M h) block index, realize_restrict M h he]
  have hv : (fun i => inclusion h (Sum.elim v (Sum.elim block index) i)) =
      Sum.elim (fun i => inclusion h (v i))
        (Sum.elim (fun j => inclusion h (block j)) (fun i => inclusion h (index i))) := by
    funext i
    rcases i with i | j
    · rfl
    · rcases j with j | j <;> rfl
  rw [hv, realize_translate]

end OneYTruth.Auxiliary
