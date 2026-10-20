/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower

/-!
# Pullback of exterior-power sheaves

The canonical comparison from the pullback of a degreewise exterior-power sheaf to the
corresponding exterior power of the pulled-back module sheaf is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorPower.Pullback

variable {X Y : RingedSpace.{u}}

/-- The component on an open set of the adjoint degreewise exterior-power pullback comparison. -/
noncomputable def app (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) (U : (Opens Y)ᵒᵖ) :
    (ExteriorPower.presheaf F n).obj U ⟶
      (((pushforward f).obj (ExteriorPower.sheaf ((pullback f).obj F) n)).val.obj U) :=
  ModuleCat.exteriorPower.mapRestrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom
      (((RingedSpace.Hom.pullbackPushforwardAdjunction f).unit.app F).val.app U) n ≫
    (ModuleCat.restrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal X.sheaf
        (ExteriorPower.presheaf ((pullback f).obj F) n)).app
        (op ((Opens.map f.hom.base).obj U.unop)))

/-- The degreewise exterior-power comparison components commute with restriction maps. -/
theorem app_naturality (f : X ⟶ Y) (F : Y.Modules) (n : ℕ)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (ExteriorPower.presheaf F n).map i ≫
        (ModuleCat.restrictScalars (Y.presheaf.map i).hom).map (app f F n V) =
      app f F n U ≫
        ((pushforward f).obj (ExteriorPower.sheaf ((pullback f).obj F) n)).val.map i := sorry

/-- The presheaf morphism adjoint to the degreewise exterior-power pullback comparison. -/
noncomputable def presheaf (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) :
    ExteriorPower.presheaf F n ⟶
      ((pushforward f).obj (ExteriorPower.sheaf ((pullback f).obj F) n)).val where
  app U := app f F n U
  naturality := app_naturality f F n

/-- The pushforward-side adjoint of the degreewise exterior-power pullback comparison. -/
noncomputable def adjoint (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) :
    ExteriorPower.sheaf F n ⟶
      (pushforward f).obj (ExteriorPower.sheaf ((pullback f).obj F) n) :=
  (SheafOfModules.RingedSite.moduleSheafificationHomEquiv Y.sheaf
    (ExteriorPower.presheaf F n)
    ((pushforward f).obj (ExteriorPower.sheaf ((pullback f).obj F) n))).symm
      (presheaf f F n)

/-- The canonical map from the pullback of a degreewise exterior-power sheaf to the exterior
power of the pulled-back module sheaf. -/
noncomputable def comparison (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) :
    (pullback f).obj (ExteriorPower.sheaf F n) ⟶
      ExteriorPower.sheaf ((pullback f).obj F) n :=
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _).symm (adjoint f F n)

/-- The adjunction sends the degreewise exterior-power pullback comparison to its named
pushforward-side adjoint. -/
theorem comparison_adj (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) :
    (RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _ (comparison f F n) =
      adjoint f F n := sorry

/-- Pullback commutes with degreewise exterior powers of module sheaves. -/
instance comparison_isIso (f : X ⟶ Y) (F : Y.Modules) (n : ℕ) :
    IsIso (comparison f F n) := sorry

end AlgebraicGeometry.RingedSpace.ExteriorPower.Pullback
