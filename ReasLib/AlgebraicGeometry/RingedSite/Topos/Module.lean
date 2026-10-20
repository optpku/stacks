/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules on site-presented ringed topoi

This file defines inverse and direct image for modules along an arbitrary morphism of
site-presented ringed topoi.  The geometric stages use the presentation-independent module
functors attached to the underlying morphism of topoi.  The remaining stages are ordinary
extension or restriction of scalars along the inverse- or direct-image structure map.

The module universe is currently the same universe `w` as the structure sheaves, matching the
available equivalence between sheaves of modules and internal module objects.

Only the scalar-extension adjunction is exposed here. The full pullback--pushforward
adjunction is constructed in the companion `Topos.ModuleAdjunction` module from the
coefficient-varying lift of the underlying topos adjunction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Pullback of modules along a morphism of ringed topoi.
First take presentation-independent inverse image over `f⁻¹𝒪_Y`, then extend scalars along
`f.structureMap : f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 03D6 "(2), ringed-topos"]
noncomputable def modulePullback
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    SheafOfModules.{w} Y.structureSheaf ⥤ SheafOfModules.{w} X.structureSheaf :=
  f.toTopos.moduleInverseImage Y.structureSheaf ⋙
    SheafOfModules.ChangeOfRings.extendScalars f.structureMap

/-- Direct image of modules along a morphism of ringed topoi.
First take presentation-independent direct image over `f_*𝒪_X`, then restrict scalars along
`f.directStructureMap : 𝒪_Y ⟶ f_*𝒪_X`. -/
@[stacks 03D6 "(1), ringed-topos"]
noncomputable def modulePushforward (f : ToposHom X Y) :
    SheafOfModules.{w} X.structureSheaf ⥤ SheafOfModules.{w} Y.structureSheaf :=
  f.toTopos.moduleDirectImage X.structureSheaf ⋙
    SheafOfModules.restrictScalars f.directStructureMap

/-- Module direct image along an arbitrary morphism of ringed topoi is additive. -/
@[stacks 03D6 "additivity of ringed-topos module direct image"]
theorem modulePushforward_additive (f : ToposHom X Y) :
    f.modulePushforward.Additive := sorry

namespace ModulePullback

/-- Pullback of modules factors as geometric inverse image followed by extension of scalars
along the inverse-image structure map. -/
theorem factorization
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    f.modulePullback =
      f.toTopos.moduleInverseImage Y.structureSheaf ⋙
        SheafOfModules.ChangeOfRings.extendScalars f.structureMap := sorry

/-- The scalar-extension stage of module pullback is left adjoint to restriction of scalars
along the inverse-image structure map. -/
@[stacks 03D6 "pullback scalar adjunction"]
noncomputable def scalarAdjunction
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    SheafOfModules.ChangeOfRings.extendScalars f.structureMap ⊣
      SheafOfModules.restrictScalars.{w} f.structureMap :=
  SheafOfModules.ChangeOfRings.extendRestrictAdjunction f.structureMap

/-- The Hom equivalence for the scalar-extension stage of module pullback. -/
noncomputable def scalarHomEquiv
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    (M : SheafOfModules.{w} (f.toTopos.ringInverseImage.obj Y.structureSheaf))
    (N : SheafOfModules.{w} X.structureSheaf) :
    ((SheafOfModules.ChangeOfRings.extendScalars f.structureMap).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars f.structureMap).obj N) :=
  (scalarAdjunction f).homEquiv M N

end ModulePullback

namespace ModulePushforward

/-- Direct image of modules factors as geometric direct image followed by restriction of
scalars along the direct-image structure map. -/
theorem factorization (f : ToposHom X Y) :
    f.modulePushforward =
      f.toTopos.moduleDirectImage X.structureSheaf ⋙
        SheafOfModules.restrictScalars f.directStructureMap := sorry

/-- Restriction along the direct-image structure map does not change the underlying
type-valued sheaf. -/
noncomputable def scalarForgetIso (f : ToposHom X Y) :
    SheafOfModules.restrictScalars f.directStructureMap ⋙
        Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf ≅
      Sheaf.InternalModule.ToInternal.underlying
        (f.toTopos.ringDirectImage.obj X.structureSheaf) :=
  Iso.refl _

/-- Forgetting module structure after ringed-topos pushforward recovers direct image of the
underlying type-valued sheaf. -/
@[stacks 03D6 "underlying sheaf of ringed-topos module direct image"]
noncomputable def forgetIso (f : ToposHom X Y) :
    f.modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf ≅
      Sheaf.InternalModule.ToInternal.underlying X.structureSheaf ⋙
        f.toTopos.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (f.toTopos.moduleDirectImage X.structureSheaf) (scalarForgetIso f) ≪≫
    f.toTopos.moduleDirectImageForgetIso X.structureSheaf

/-- The underlying-sheaf comparison for ringed-topos module pushforward is natural in a
module morphism. -/
theorem forgetIso_naturality
    (f : ToposHom X Y) {M N : SheafOfModules.{w} X.structureSheaf} (g : M ⟶ N) :
    (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).map
          (f.modulePushforward.map g) ≫
        (forgetIso f).hom.app N =
      (forgetIso f).hom.app M ≫
        f.toTopos.pushforward.map
          ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).map g) := sorry

end ModulePushforward

end RingedSite.ToposHom
