/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Colimit

/-!
# Direct-image stage families on a cofiltered colimit site

This leaf packages the direct images of a sheaf on a cofiltered colimit site
as a compatible stage family.  It separates the formal transition data from
the cocone-pullback and colimit capabilities needed to form its counit
comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u uI uC vC w

namespace CategoryTheory

namespace CofilteredSiteDiagram

namespace StageFamily

namespace DirectImage

/-- The direct-image functor from the colimit site to stage `i`. -/
abbrev pushforward
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    (i : S.I) :
    Sheaf S.colimitTopology A ⥤ Sheaf (S.stageTopology i) A :=
  (S.stageCoconeFunctor i).sheafPushforwardContinuous
    A (S.stageTopology i) S.colimitTopology

/-- The sheaf pullback from stage `i` to the colimit site. -/
noncomputable abbrev pullback
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    [ColimitSheafPullback S A] (i : S.I) :
    Sheaf (S.stageTopology i) A ⥤ Sheaf S.colimitTopology A :=
  (S.stageCoconeFunctor i).sheafPullback
    A (S.stageTopology i) S.colimitTopology

/-- Direct image from the colimit site commutes with a stage transition. -/
noncomputable def pushforwardCompIso
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    {i j : S.I} (a : j ⟶ i) :
    pushforward A j ⋙
        (S.stageFunctor a).sheafPushforwardContinuous
          A (S.stageTopology i) (S.stageTopology j) ≅
      pushforward A i :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso (S.stageCoconeFunctor_comp_eq a))
    A (S.stageTopology i) (S.stageTopology j) S.colimitTopology

/-- The transition map between direct images of a colimit-site sheaf. -/
noncomputable def transition
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : Sheaf S.colimitTopology A)
    {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    (StageSheafPullback.functor A a).obj ((pushforward A i).obj F) ⟶
      (pushforward A j).obj F :=
  (((S.stageFunctor a).sheafAdjunctionContinuous
      A (S.stageTopology i) (S.stageTopology j)).homEquiv
      ((pushforward A i).obj F) ((pushforward A j).obj F)).symm
    ((pushforwardCompIso A a).inv.app F)

/-- The direct-image transition at an identity arrow is the canonical identity-pullback map. -/
theorem transition_id
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : Sheaf S.colimitTopology A) (i : S.I)
    [StageSheafPullback S A (𝟙 i)] :
    transition F (𝟙 i) =
      (StageSheafPullback.idIso A i).hom.app ((pushforward A i).obj F) := sorry

/-- Direct-image transitions satisfy the compatible-stage-family cocycle condition. -/
theorem transition_comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : Sheaf S.colimitTopology A)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    [StageSheafPullback S A a]
    [StageSheafPullback S A b]
    [StageSheafPullback S A (b ≫ a)] :
    (StageSheafPullback.compIso A a b).hom.app ((pushforward A i).obj F) ≫
        transition F (b ≫ a) =
      (StageSheafPullback.functor A b).map (transition F a) ≫ transition F b := sorry

/-- The compatible stage family formed by direct images of `F`. -/
noncomputable def family
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : Sheaf S.colimitTopology A) : StageFamily S A where
  obj i := (pushforward A i).obj F
  transition a := transition F a
  transition_id i := transition_id F i
  transition_comp a b := transition_comp F a b

/-- The counit of the stage-`i` pullback/direct-image adjunction. -/
noncomputable abbrev counit
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    (F : Sheaf S.colimitTopology A) (i : S.I) :
    (pullback A i).obj ((pushforward A i).obj F) ⟶ F :=
  ((S.stageCoconeFunctor i).sheafAdjunctionContinuous
    A (S.stageTopology i) S.colimitTopology).counit.app F

/-- The stage counits are natural for the diagram of the direct-image family. -/
theorem counit_naturality
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    (F : Sheaf S.colimitTopology A)
    {i j : S.Iᵒᵖ} (a : i ⟶ j) :
    (StageFamily.diagram (family F)).map a ≫ counit F j.unop =
      counit F i.unop ≫ ((Functor.const S.Iᵒᵖ).obj F).map a := sorry

/-- The cocone of stage counits from the direct-image family diagram to `F`. -/
noncomputable def counitCocone
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    (F : Sheaf S.colimitTopology A) : Cocone (StageFamily.diagram (family F)) where
  pt := F
  ι :=
    { app := fun i ↦ counit F i.unop
      naturality := fun _ _ a ↦ counit_naturality F a }

/-- The colimit-site sheaf assembled from the direct-image compatible family. -/
noncomputable abbrev colimitSheaf
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology A)]
    (F : Sheaf S.colimitTopology A) : Sheaf S.colimitTopology A :=
  StageFamily.colimitSheaf (family F)

/-- The canonical map from the colimit of the direct-image family back to `F`. -/
noncomputable abbrev comparison
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology A)]
    (F : Sheaf S.colimitTopology A) :
    colimitSheaf F ⟶ F :=
  colimit.desc (StageFamily.diagram (family F)) (counitCocone F)

/-- The direct-image colimit comparison restricts to the counit on each summand. -/
theorem comparison_ι
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology A)]
    (F : Sheaf S.colimitTopology A) (i : S.Iᵒᵖ) :
    colimit.ι (StageFamily.diagram (family F)) i ≫ comparison F = counit F i.unop := sorry

/-- Lemma 7.18.5 (0EXJ): the direct-image colimit comparison for a set-valued sheaf on the
colimit site is an isomorphism. -/
@[stacks 0EXJ]
theorem comparison_isIso
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (F : Sheaf S.colimitTopology (Type u)) :
    IsIso (comparison F) := sorry

attribute [instance] comparison_isIso

end DirectImage

end StageFamily

end CofilteredSiteDiagram

end CategoryTheory
