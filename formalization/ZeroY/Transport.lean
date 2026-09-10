import Lean

/-!
# 关系与展开的通用传输

本文件只证明带有显式前提的通用定理。具体山脉编码的往返、保序和展开共轭
仍须分别证明，才能把这里的接口用于 0-Y 与 BMS。

严格关系的参数顺序统一为“小者、大者”；展开函数的参数顺序为“表达式、指标”。
-/

namespace ZeroY

universe u v

variable {α : Type u} {β : Type v}
variable {source : α → α → Prop} {target : β → β → Prop}

/-- 显式携带两边逆映射及严格关系等价的同构，不依赖线序类型类。 -/
structure StrictRelationIso (α : Type u) (β : Type v)
    (source : α → α → Prop) (target : β → β → Prop) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  rel_iff : ∀ x y, target (toFun x) (toFun y) ↔ source x y

/-- 保持严格关系的映射可反向传输可达性；这里不需要映射单射。 -/
theorem accessible_of_relation_map (encode : α → β)
    (hMap : ∀ {x y}, source x y → target (encode x) (encode y))
    {bound : β} (hAccessible : Acc target bound) :
    ∀ x, encode x = bound → Acc source x := by
  induction hAccessible with
  | intro bound _ ih =>
      intro x hEncode
      apply Acc.intro x
      intro smaller hSmaller
      apply ih (encode smaller)
      · rw [← hEncode]
        exact hMap hSmaller
      · rfl

/-- 目标关系良基且编码保持关系，则源关系良基。 -/
theorem wellFounded_of_relation_map (encode : α → β)
    (hMap : ∀ {x y}, source x y → target (encode x) (encode y))
    (hWellFounded : WellFounded target) : WellFounded source := by
  constructor
  intro x
  exact accessible_of_relation_map encode hMap
    (hWellFounded.apply (encode x)) x rfl

namespace StrictRelationIso

/-- 左逆给出编码单射。 -/
theorem injective (equivalence : StrictRelationIso α β source target)
    {x y : α} (hEqual : equivalence.toFun x = equivalence.toFun y) : x = y := by
  calc
    x = equivalence.invFun (equivalence.toFun x) := (equivalence.left_inv x).symm
    _ = equivalence.invFun (equivalence.toFun y) := congrArg equivalence.invFun hEqual
    _ = y := equivalence.left_inv y

/-- 逆映射也保持并反射严格关系。 -/
theorem inv_rel_iff (equivalence : StrictRelationIso α β source target)
    (x y : β) :
    source (equivalence.invFun x) (equivalence.invFun y) ↔ target x y := by
  have hRelation := equivalence.rel_iff (equivalence.invFun x) (equivalence.invFun y)
  rw [equivalence.right_inv x, equivalence.right_inv y] at hRelation
  exact hRelation.symm

/-- 交换编码和解码得到反向同构。 -/
def symm (equivalence : StrictRelationIso α β source target) :
    StrictRelationIso β α target source where
  toFun := equivalence.invFun
  invFun := equivalence.toFun
  left_inv := equivalence.right_inv
  right_inv := equivalence.left_inv
  rel_iff := equivalence.inv_rel_iff

/-- 同构两边的严格关系同时良基。 -/
theorem wellFounded_iff (equivalence : StrictRelationIso α β source target) :
    WellFounded source ↔ WellFounded target := by
  constructor
  · intro hWellFounded
    exact wellFounded_of_relation_map equivalence.invFun
      (fun {x y} hRelation => (equivalence.inv_rel_iff x y).mpr hRelation)
      hWellFounded
  · intro hWellFounded
    exact wellFounded_of_relation_map equivalence.toFun
      (fun {x y} hRelation => (equivalence.rel_iff x y).mpr hRelation)
      hWellFounded

end StrictRelationIso

/-- 选择一个自然数指标进行一次展开，并排除展开不改变表达式的情况。 -/
def ExpansionStep (expand : α → Nat → α) (smaller larger : α) : Prop :=
  (∃ index, expand larger index = smaller) ∧ smaller ≠ larger

/-- 单射编码与展开共轭时，源系统的非平凡一步展开映到目标系统。 -/
theorem expansionStep_map
    (sourceExpand : α → Nat → α) (targetExpand : β → Nat → β)
    (encode : α → β)
    (hInjective : ∀ {x y}, encode x = encode y → x = y)
    (hConjugate : ∀ x index,
      encode (sourceExpand x index) = targetExpand (encode x) index)
    {smaller larger : α} (hStep : ExpansionStep sourceExpand smaller larger) :
    ExpansionStep targetExpand (encode smaller) (encode larger) := by
  rcases hStep with ⟨⟨index, hExpanded⟩, hDifferent⟩
  constructor
  · refine ⟨index, ?_⟩
    rw [← hConjugate larger index, hExpanded]
  · intro hEqual
    exact hDifferent (hInjective hEqual)

/-- 共轭与单射还反射编码像中的非平凡一步展开，不需要目标上的满射。 -/
theorem expansionStep_iff
    (sourceExpand : α → Nat → α) (targetExpand : β → Nat → β)
    (encode : α → β)
    (hInjective : ∀ {x y}, encode x = encode y → x = y)
    (hConjugate : ∀ x index,
      encode (sourceExpand x index) = targetExpand (encode x) index)
    (smaller larger : α) :
    ExpansionStep targetExpand (encode smaller) (encode larger) ↔
      ExpansionStep sourceExpand smaller larger := by
  constructor
  · rintro ⟨⟨index, hExpanded⟩, hDifferent⟩
    constructor
    · refine ⟨index, hInjective ?_⟩
      rw [hConjugate larger index]
      exact hExpanded
    · intro hEqual
      exact hDifferent (congrArg encode hEqual)
  · exact expansionStep_map sourceExpand targetExpand encode hInjective hConjugate

/-- 单射共轭把目标展开的良基性传给源展开。 -/
theorem expansionWellFounded_of_injective_conjugacy
    (sourceExpand : α → Nat → α) (targetExpand : β → Nat → β)
    (encode : α → β)
    (hInjective : ∀ {x y}, encode x = encode y → x = y)
    (hConjugate : ∀ x index,
      encode (sourceExpand x index) = targetExpand (encode x) index)
    (hWellFounded : WellFounded (ExpansionStep targetExpand)) :
    WellFounded (ExpansionStep sourceExpand) := by
  exact wellFounded_of_relation_map encode
    (expansionStep_map sourceExpand targetExpand encode hInjective hConjugate)
    hWellFounded

end ZeroY
