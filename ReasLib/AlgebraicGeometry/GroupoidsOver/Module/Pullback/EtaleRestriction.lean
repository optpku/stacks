/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-! # Étale restriction of module pullback -/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- The structure-sheaf maps for pullback and change of topology commute under
the canonical identification of their composite base functors. -/
private theorem modulePullbackRestriction_coefficient (f : X ⟶ Y) :
    let cF := Functor.isContinuous_comp (toFunctor f) (𝟭 Y.total)
      X.etaleTopology Y.etaleTopology (fppfTopology Y)
    let cG := Functor.isContinuous_comp (𝟭 X.total) (toCartesianBasedFunctor f).toFunctor
      X.etaleTopology (fppfTopology X) (fppfTopology Y)
    let e := rightUnitor (toFunctor f) ≪≫ (eqToIso (cartesian_toFunctor_eq f)).symm ≪≫
      (leftUnitor (toCartesianBasedFunctor f).toFunctor).symm
    (etaleToFppfStructureSheafMap X ≫
      ((𝟭 X.total).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology (fppfTopology X)).map (structureSheafMap f)) ≫
      (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _ e.hom RingCat.{u} _
        X.etaleTopology (fppfTopology Y) cF cG).app (structureSheaf Y) =
      etaleSiteHom_structureSheafMap f ≫
        ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
          X.etaleTopology Y.etaleTopology).map (etaleToFppfStructureSheafMap Y) := sorry

/-- Pullback of fppf modules followed by étale restriction is canonically
isomorphic to étale restriction followed by étale inverse image. -/
def modulePullbackRestrictionIso (f : X ⟶ Y) :
    modulePullback f ⋙ restriction X ≅ restriction Y ⋙ etaleModuleInverseImage f :=
  let cF := Functor.isContinuous_comp (toFunctor f) (𝟭 Y.total)
    X.etaleTopology Y.etaleTopology (fppfTopology Y)
  let cG := Functor.isContinuous_comp (𝟭 X.total) (toCartesianBasedFunctor f).toFunctor
    X.etaleTopology (fppfTopology X) (fppfTopology Y)
  let e := rightUnitor (toFunctor f) ≪≫ (eqToIso (cartesian_toFunctor_eq f)).symm ≪≫
    (leftUnitor (toCartesianBasedFunctor f).toFunctor).symm
  SheafOfModules.pushforwardComp (etaleToFppfStructureSheafMap X) (structureSheafMap f) ≪≫
    @SheafOfModules.pushforwardCongr₂ _ _ _ _ X.etaleTopology (fppfTopology Y)
      _ _ _ _ cF cG _ _ e (modulePullbackRestriction_coefficient f) ≪≫
    (SheafOfModules.pushforwardComp (etaleSiteHom_structureSheafMap f)
      (etaleToFppfStructureSheafMap Y)).symm

end AlgebraicGeometry.GroupoidsOver
