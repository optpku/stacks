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

universe uX vX uY vY uZ vZ w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]
  [@GrothendieckTopology.HasSheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w})]

/-- Pullback of modules along a morphism of ringed topoi.
First take presentation-independent inverse image over `f⁻¹𝒪_Y`, then extend scalars along
`f.structureMap : f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 03D6 "(2), ringed-topos"]
noncomputable def modulePullback
    (f : ToposHom X Y)
    [((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).IsRightAdjoint] :
    (@_root_.SheafOfModules.{w} Y.carrier Y.carrier.str Y.siteTopology Y.structureSheaf) ⥤ (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf) :=
  (@MorphismOfTopoiIn.moduleInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos Y.structureSheaf) ⋙
    (@SheafOfModules.ChangeOfRings.extendScalars X.carrier X.carrier.str X.siteTopology _ _ f.structureMap inferInstance)

/-- Direct image of modules along a morphism of ringed topoi.
First take presentation-independent direct image over `f_*𝒪_X`, then restrict scalars along
`f.directStructureMap : 𝒪_Y ⟶ f_*𝒪_X`. -/
@[stacks 03D6 "(1), ringed-topos"]
noncomputable def modulePushforward (f : ToposHom X Y) :
    (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf) ⥤ (@_root_.SheafOfModules.{w} Y.carrier Y.carrier.str Y.siteTopology Y.structureSheaf) :=
  (@MorphismOfTopoiIn.moduleDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos X.structureSheaf) ⋙
    (@SheafOfModules.restrictScalars.{w} Y.carrier Y.carrier.str Y.siteTopology _ _ f.directStructureMap)

/-- Module direct image along an arbitrary morphism of ringed topoi is additive. -/
@[stacks 03D6 "additivity of ringed-topos module direct image"]
theorem modulePushforward_additive (f : ToposHom X Y) :
    f.modulePushforward.Additive := sorry

namespace ModulePullback

/-- Pullback of modules factors as geometric inverse image followed by extension of scalars
along the inverse-image structure map. -/
theorem factorization
    (f : ToposHom X Y)
    [((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).IsRightAdjoint] :
    f.modulePullback =
      (@MorphismOfTopoiIn.moduleInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos Y.structureSheaf) ⋙
        (@SheafOfModules.ChangeOfRings.extendScalars X.carrier X.carrier.str X.siteTopology _ _ f.structureMap inferInstance) := sorry

/-- The scalar-extension stage of module pullback is left adjoint to restriction of scalars
along the inverse-image structure map. -/
@[stacks 03D6 "pullback scalar adjunction"]
noncomputable def scalarAdjunction
    (f : ToposHom X Y)
    [((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).IsRightAdjoint] :
    (@SheafOfModules.ChangeOfRings.extendScalars X.carrier X.carrier.str X.siteTopology _ _ f.structureMap inferInstance) ⊣
      (@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap) :=
  (@SheafOfModules.ChangeOfRings.extendRestrictAdjunction X.carrier X.carrier.str X.siteTopology _ _ f.structureMap inferInstance)

/-- The Hom equivalence for the scalar-extension stage of module pullback. -/
noncomputable def scalarHomEquiv
    (f : ToposHom X Y)
    [((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).IsRightAdjoint]
    (M : (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology ((@MorphismOfTopoiIn.ringInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).obj Y.structureSheaf)))
    (N : (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf)) :
    (((@SheafOfModules.ChangeOfRings.extendScalars X.carrier X.carrier.str X.siteTopology _ _ f.structureMap inferInstance)).obj M ⟶ N) ≃
      (M ⟶ ((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).obj N) :=
  (scalarAdjunction f).homEquiv M N

end ModulePullback

namespace ModulePushforward

/-- Direct image of modules factors as geometric direct image followed by restriction of
scalars along the direct-image structure map. -/
theorem factorization (f : ToposHom X Y) :
    f.modulePushforward =
      (@MorphismOfTopoiIn.moduleDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos X.structureSheaf) ⋙
        (@SheafOfModules.restrictScalars.{w} Y.carrier Y.carrier.str Y.siteTopology _ _ f.directStructureMap) := sorry

/-- Restriction along the direct-image structure map does not change the underlying
type-valued sheaf. -/
noncomputable def scalarForgetIso (f : ToposHom X Y) :
    (@SheafOfModules.restrictScalars.{w} Y.carrier Y.carrier.str Y.siteTopology _ _ f.directStructureMap) ⋙
        (@Sheaf.InternalModule.ToInternal.underlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf) ≅
      (@Sheaf.InternalModule.ToInternal.underlying Y.carrier Y.carrier.str Y.siteTopology inferInstance
        ((@MorphismOfTopoiIn.ringDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).obj X.structureSheaf)) :=
  Iso.refl _

/-- Forgetting module structure after ringed-topos pushforward recovers direct image of the
underlying type-valued sheaf. -/
@[stacks 03D6 "underlying sheaf of ringed-topos module direct image"]
noncomputable def forgetIso (f : ToposHom X Y) :
    f.modulePushforward ⋙
        (@Sheaf.InternalModule.ToInternal.underlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf) ≅
      (@Sheaf.InternalModule.ToInternal.underlying X.carrier X.carrier.str X.siteTopology inferInstance X.structureSheaf) ⋙
        f.toTopos.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((@MorphismOfTopoiIn.moduleDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos X.structureSheaf)) (scalarForgetIso f) ≪≫
    (@MorphismOfTopoiIn.moduleDirectImageForgetIso Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology inferInstance inferInstance f.toTopos X.structureSheaf)

/-- Forgetting module structure after two successive ringed-topos pushforwards recovers
direct image of the underlying type-valued sheaf along the composite morphism. -/
noncomputable def compForgetIso
    {Z : RingedSite.{uZ, vZ, w}}
    [@GrothendieckTopology.HasSheafCompose Z.carrier Z.carrier.str RingCat.{w}
      inferInstance (Type w) inferInstance Z.siteTopology (forget RingCat.{w})]
    (f : ToposHom X Y) (g : ToposHom Y Z) :
    f.modulePushforward ⋙ g.modulePushforward ⋙
        (@Sheaf.InternalModule.ToInternal.underlying Z.carrier Z.carrier.str
          Z.siteTopology inferInstance Z.structureSheaf) ≅
      (@Sheaf.InternalModule.ToInternal.underlying X.carrier X.carrier.str
        X.siteTopology inferInstance X.structureSheaf) ⋙
        (ToposHom.comp f g).toTopos.pushforward :=
  Functor.associator f.modulePushforward g.modulePushforward
      (Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf) ≪≫
    Functor.isoWhiskerLeft f.modulePushforward (forgetIso g) ≪≫
    (Functor.associator f.modulePushforward
      (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf)
      g.toTopos.pushforward).symm ≪≫
    Functor.isoWhiskerRight (forgetIso f) g.toTopos.pushforward ≪≫
    Functor.associator (Sheaf.InternalModule.ToInternal.underlying X.structureSheaf)
      f.toTopos.pushforward g.toTopos.pushforward

/-- The underlying-sheaf comparison for ringed-topos module pushforward is natural in a
module morphism. -/
theorem forgetIso_naturality
    (f : ToposHom X Y) {M N : (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf)} (g : M ⟶ N) :
    ((@Sheaf.InternalModule.ToInternal.underlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf)).map
          (f.modulePushforward.map g) ≫
        (forgetIso f).hom.app N =
      (forgetIso f).hom.app M ≫
        f.toTopos.pushforward.map
          (((@Sheaf.InternalModule.ToInternal.underlying X.carrier X.carrier.str X.siteTopology inferInstance X.structureSheaf)).map g) := sorry

end ModulePushforward

end RingedSite.ToposHom
