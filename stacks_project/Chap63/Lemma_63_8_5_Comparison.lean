/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek.BaseChange
public import stacks_project.Chap63.Lemma_63_8_5_Pullback

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (Λ : Type u) [Ring Λ]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]

/- The module-valued ordinary base-change mate. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleModulePushforwardBaseChange f g f' g' h_cart Λ :
  etaleModulePushforward f Λ ⋙ etaleModuleSheafPullback g Λ ⟶
    etaleModuleSheafPullback g' Λ ⋙ etaleModulePushforward f' Λ)

/- The comparison is the right mate of the inverse-image square. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleModulePushforwardBaseChange_eq f g f' g' h_cart Λ :
  etaleModulePushforwardBaseChange f g f' g' h_cart Λ =
    DerivedBaseChange.map
      ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)
      ((smallEtalePullback f').sheafAdjunctionContinuous (ModuleCat.{u} Λ)
        Y'.smallEtaleTopology X'.smallEtaleTopology)
      (etaleModuleSheafPullback_square f g f' g' h_cart Λ))

end AlgebraicGeometry.Scheme.Etale

end
