import ZeroY
import ZeroY.Dynamics.Equivalence
import ZeroY.Dynamics.Termination
import ZeroY.Wiki.WellFounded
import ZeroY.Wiki.Termination
import BMSConstructibleBridge.FinalAssembly

/-!
# 接入上游构造宇宙的具体降界模型

这里的定理没有把表示降界系统列为用户需要另证的前提。
-/

namespace ZeroY.Concrete

open YesMetaZFC.BMS
open YesMetaZFC.BMS.ConstructibleBridge
open YesMetaZFC.BMS.StabilityFrame

theorem bms_step_wellFounded : WellFounded Step :=
  ZeroY.BMS.step_wellFounded_any
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem bms_descendants_strictWellOrder (root : ValidArray) :
    StrictWellOrder (ZeroY.BMS.Descendant root) ZeroY.BMS.DescendantLt :=
  ZeroY.BMS.descendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem root

theorem bms_generated_strictWellOrder :
    StrictWellOrder GeneratedArray ZeroY.BMS.GeneratedMatrixLt :=
  ZeroY.BMS.generatedMatrix_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_step_wellFounded : WellFounded YStep :=
  ZeroY.yStep_wellFounded reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_generated_strictWellOrder : StrictWellOrder YGeneratedExpr YGeneratedLt :=
  ZeroY.yGenerated_strictWellOrder reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_descendants_strictWellOrder (root : Expr) :
    StrictWellOrder (YDescendant root) YDescendantLt :=
  ZeroY.yDescendants_strictWellOrder reflectionData_l.wellOrderingModel.representationDescentSystem root

theorem no_infinite_y_step_chain :
    ¬ ∃ chain : Nat → Expr, ∀ index, YStep (chain (index + 1)) (chain index) :=
  ZeroY.no_infinite_yStep_chain reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_trajectory_terminates (initial : Expr) (indices : Nat → Nat) :
    ∃ step, (yTrajectory initial indices step).values = [] :=
  ZeroY.yTrajectory_terminates reflectionData_l.wellOrderingModel.representationDescentSystem initial indices

theorem wiki_step_wellFounded : WellFounded WikiStep :=
  ZeroY.wikiStep_wellFounded reflectionData_l.wellOrderingModel.representationDescentSystem

theorem wiki_generated_strictWellOrder : StrictWellOrder WikiGeneratedExpr WikiGeneratedLt :=
  ZeroY.wikiGenerated_strictWellOrder reflectionData_l.wellOrderingModel.representationDescentSystem

theorem wiki_descendants_strictWellOrder (root : Expr) :
    StrictWellOrder (WikiDescendant root) WikiDescendantLt :=
  ZeroY.wikiDescendants_strictWellOrder reflectionData_l.wellOrderingModel.representationDescentSystem root

theorem no_infinite_wiki_step_chain :
    ¬ ∃ chain : Nat → Expr, ∀ index, WikiStep (chain (index + 1)) (chain index) :=
  ZeroY.no_infinite_wikiStep_chain reflectionData_l.wellOrderingModel.representationDescentSystem

theorem wiki_trajectory_terminates (initial : Expr) (indices : Nat → Nat) :
    ∃ step, (wikiTrajectory initial indices step).values = [] :=
  ZeroY.wikiTrajectory_terminates reflectionData_l.wellOrderingModel.representationDescentSystem initial indices

end ZeroY.Concrete
