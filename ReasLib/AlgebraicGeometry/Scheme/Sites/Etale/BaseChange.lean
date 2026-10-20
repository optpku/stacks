/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.CategoryTheory.Sites.Over.BaseChange

/-!
# Base change for étale topoi

Cartesian squares of schemes induce the mixed small-to-big base-change identification for
étale direct and inverse images.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

variable {S S' T T' : Scheme.{u}}

/-- In a cartesian square of schemes, big étale direct image followed by small-to-big inverse
image is isomorphic to small-to-big inverse image followed by small étale direct image. -/
theorem pushforwardBaseChange_isomorphic
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (hcart : IsPullback g' f' f g) :
    IsIsomorphic
      ((Etale.Big.morphismOfTopoi f) _* ⋙
        (Etale.SmallToBig.morphismOfTopoi g)⁻¹)
      ((Etale.SmallToBig.morphismOfTopoi g')⁻¹ ⋙
        (Etale.SmallToBig.smallMorphism f') _*) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig

namespace AlgebraicGeometry.Scheme

variable {X Y V : Scheme.{u}}

/-- Inverse image along a morphism of schemes commutes with étale extension by zero
for sheaves of abelian groups, up to a natural isomorphism. -/
theorem abelianExtensionByZero_baseChange
    (f : Y ⟶ X) (j : V ⟶ X) [Etale j]
    [∀ F : (pullback f j).Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction (pullback.fst f j)).op.HasLeftKanExtension F]
    [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [Functor.IsRightAdjoint ((smallEtalePullback (pullback.snd f j)).sheafPushforwardContinuous
      AddCommGrpCat.{w} V.smallEtaleTopology (pullback f j).smallEtaleTopology)]
    [Functor.IsRightAdjoint ((smallEtalePullback f).sheafPushforwardContinuous
      AddCommGrpCat.{w} X.smallEtaleTopology Y.smallEtaleTopology)] :
    Nonempty (
      (smallEtalePullback (pullback.snd f j)).sheafPullback
          AddCommGrpCat.{w} V.smallEtaleTopology
          (pullback f j).smallEtaleTopology ⋙
        abelianExtensionByZero (pullback.fst f j) ≅
      abelianExtensionByZero j ⋙
        (smallEtalePullback f).sheafPullback AddCommGrpCat.{w}
          X.smallEtaleTopology Y.smallEtaleTopology) := sorry

/-- Inverse image along a morphism of schemes commutes with étale extension by zero
for sheaves of modules over a ring, up to a natural isomorphism. -/
theorem moduleExtensionByZero_baseChange
    {Λ : Type w} [Ring Λ]
    (f : Y ⟶ X) (j : V ⟶ X) [Etale j]
    [∀ F : (pullback f j).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction (pullback.fst f j)).op.HasLeftKanExtension F]
    [∀ F : V.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [Functor.IsRightAdjoint ((smallEtalePullback (pullback.snd f j)).sheafPushforwardContinuous
      (ModuleCat.{w} Λ) V.smallEtaleTopology (pullback f j).smallEtaleTopology)]
    [Functor.IsRightAdjoint ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{w} Λ) X.smallEtaleTopology Y.smallEtaleTopology)] :
    Nonempty (
      (smallEtalePullback (pullback.snd f j)).sheafPullback
          (ModuleCat.{w} Λ) V.smallEtaleTopology
          (pullback f j).smallEtaleTopology ⋙
        moduleExtensionByZero (pullback.fst f j) ≅
      moduleExtensionByZero j ⋙
        (smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology) := sorry

end AlgebraicGeometry.Scheme
