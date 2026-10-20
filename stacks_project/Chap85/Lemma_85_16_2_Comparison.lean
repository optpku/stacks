/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Comparison
public import stacks_project.Chap85.Lemma_85_16_1_Localization

/-!
# Degreewise inverse image and abelian equalizer comparison for total localization

The restriction, coface, and equalizer comparison constructions are available through
this chapter import together with the localization interface.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
open scoped Simplicial

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))

/- Fiber inclusion is continuous for the stage and total topologies. -/
#check (CategoryTheory.SemiRepresentableFamily.overSite_ι_isContinuous J K :
  ∀ n : SimplexCategory,
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K))

/- Fiber inclusion is cocontinuous for the stage and total topologies. -/
#check (CategoryTheory.SemiRepresentableFamily.overSite_ι_isCocontinuous J K :
  ∀ n : SimplexCategory,
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K))

/- Fiber localization agrees with stage localization. -/
#check (CategoryTheory.SemiRepresentableFamily.fiber_comp_totalForget K :
  ∀ n : SimplexCategory,
    Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K ≅ forget (K.obj (op n)))

/- Fiber localization is continuous. -/
#check (CategoryTheory.SemiRepresentableFamily.fiber_comp_isContinuous J K :
  ∀ n : SimplexCategory,
    (Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K).IsContinuous
      (overTopology J (K.obj (op n))) J)

/- Total inverse image restricts degreewise to stage inverse image. -/
#check (CategoryTheory.SemiRepresentableFamily.sheafInverseImage_fiberRestrict J K :
  ∀ n : SimplexCategory,
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology J K) J ⋙ sheafFiberRestrict J K n ≅
      sheafStageRestrict J K n)

/- A coface followed by fiber inclusion is continuous. -/
#check (CategoryTheory.SemiRepresentableFamily.overSiteFace_comp_ι_isContinuous J K :
  ∀ i : Fin 2,
    (overSiteFace K i ⋙ Grothendieck.ι (overSiteDiagram K) (op ⦋0⦌)).IsContinuous
      (overTopology J (K.obj (op ⦋1⦌))) (overSiteTotalTopology J K))

/- Stage direct image is cocontinuous sheaf pushforward. -/
#check (CategoryTheory.SemiRepresentableFamily.abelianStagePushforward J K :
  ∀ (n : SimplexCategory)
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P],
    Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} ⥤
      Sheaf J AddCommGrpCat.{max w u v})

end CategoryTheory.SemiRepresentableFamily
