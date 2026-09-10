import ZeroY.Wiki
import ZeroY.Dynamics.Equivalence

/-!
# Wiki 端点系统的良基性与良序

数值端点定义与闭包等价已经独立完成。本文件只沿已证明的有限路径与
序同构传输良基性，不把 Wiki 的展开关系定义为 BMS 关系。
-/

namespace ZeroY

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

abbrev WikiGeneratedExpr := { s : Expr // WikiGenerated s }
abbrev WikiDescendant (root : Expr) := { s : Expr // WikiExpansionPath root s }

def WikiGeneratedLt (left right : WikiGeneratedExpr) : Prop := ExprLt left.val right.val
def WikiDescendantLt {root : Expr} (left right : WikiDescendant root) : Prop :=
  ExprLt left.val right.val

def wikiGeneratedOrderIso :
    StrictRelationIso WikiGeneratedExpr YGeneratedExpr WikiGeneratedLt YGeneratedLt where
  toFun := fun s => ⟨s.val, (wikiGenerated_iff_yGenerated s.val).mp s.property⟩
  invFun := fun s => ⟨s.val, (wikiGenerated_iff_yGenerated s.val).mpr s.property⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  rel_iff := fun _ _ => Iff.rfl

def wikiDescendantOrderIso (root : Expr) :
    StrictRelationIso (WikiDescendant root) (YDescendant root) WikiDescendantLt YDescendantLt where
  toFun := fun s => ⟨s.val, (wikiPath_iff_yPath root s.val).mp s.property⟩
  invFun := fun s => ⟨s.val, (wikiPath_iff_yPath root s.val).mpr s.property⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  rel_iff := fun _ _ => Iff.rfl

universe u

/-- Wiki 任意合法起点的非平凡一步展开关系良基。 -/
theorem wikiStep_wellFounded {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : WellFounded WikiStep :=
  wellFounded_of_relation_map id wikiStep_transGen_yStep (yStep_wellFounded system).transGen

theorem wikiGenerated_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : StrictWellOrder WikiGeneratedExpr WikiGeneratedLt where
  wellFounded := wikiGeneratedOrderIso.wellFounded_iff.mpr
    (yGenerated_strictWellOrder system).wellFounded
  transitive := fun hFirst hSecond => exprLt_trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

/-- 每个固定合法起点的全部 Wiki 后代按字典序良序。 -/
theorem wikiDescendants_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (root : Expr) :
    StrictWellOrder (WikiDescendant root) WikiDescendantLt where
  wellFounded := (wikiDescendantOrderIso root).wellFounded_iff.mpr
    (yDescendants_strictWellOrder system root).wellFounded
  transitive := fun hFirst hSecond => exprLt_trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

theorem no_infinite_wikiStep_chain {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → Expr, ∀ index, WikiStep (chain (index + 1)) (chain index) := by
  rintro ⟨chain, hStep⟩
  have hNoChain : ∀ s, Acc WikiStep s → ∀ index, chain index ≠ s := by
    intro s hAcc
    induction hAcc with
    | intro s _ ih =>
        intro index hEqual
        apply ih (chain (index + 1))
        · rw [← hEqual]
          exact hStep index
        · rfl
  exact hNoChain _ ((wikiStep_wellFounded system).apply (chain 0)) 0 rfl

end ZeroY
