module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackSmallSource
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# The opens ringed site of a ringed space

This module provides the canonical passage from a ringed space to the ringed site of its open
subsets.  It also records the module-category instances that are definitionally inherited across
that passage.
-/

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open scoped RingedSite.Hom RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The morphism of opens ringed sites induced by a morphism of ringed spaces. -/
abbrev opensRingedSiteHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := TopologicalSpace.Opens.map f.hom.base
  isMorphismOfSites := inferInstance
  structureSheafMap := RingedSpace.Hom.toRingCatSheafHom f

namespace opensRingedSiteHom

/-- Pullback of sheaves of types along an opens-ringed-site morphism preserves finite limits.
This named instance fixes the canonical presentation used by the associated topos morphism. -/
@[stacks 03D6 "finite-limit preservation on opens sites"]
instance typePullback_preservesFiniteLimits
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    CategoryTheory.Limits.PreservesFiniteLimits
      ((opensRingedSiteHom f).base.sheafPullback (Type u)
        (opensRingedSite Y).siteTopology (opensRingedSite X).siteTopology) := sorry

end opensRingedSiteHom

/-- The morphism of topoi presented by the opens-ringed-site morphism of `f`.  The presentation
universe is fixed canonically, so downstream declarations do not expose an artificial universe
or finite-limit-preservation parameter. -/
noncomputable abbrev opensMorphismOfTopoi {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    CategoryTheory.MorphismOfTopoiIn
      (opensRingedSite Y).siteTopology (opensRingedSite X).siteTopology :=
  RingedSite.Hom.toMorphismOfTopoi.{u, u, u, u, u, u} (opensRingedSiteHom f)

namespace opensRingedSiteHom

/-- Direct image of commutative-ring sheaves along the base functor of an opens-ringed-site
morphism has its canonical sheaf pullback as a left adjoint.  This named specialization keeps
typeclass search from rediscovering the large generic Kan-extension instance at each use. -/
@[stacks 03D6 "commutative-ring pullback on opens sites"]
instance commRingPushforward_isRightAdjoint
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ((opensRingedSiteHom f).base.sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsRightAdjoint := sorry

/-- The opens-site pullback induced by `f` inherits additivity from the usual pullback `pullback f` on
sheaves of modules. -/
instance pullback_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] :
    (SheafOfModules.pullback (opensRingedSiteHom f).structureSheafMap).Additive := sorry

/-- The opens-site pushforward induced by `f` inherits additivity from the usual pushforward
`pushforward f` on sheaves of modules. -/
instance modulePushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSite.Hom.modulePushforward (opensRingedSiteHom f)).Additive := sorry

/-- Direct image along a composite of opens-ringed-site morphisms has the actual
free-presentation left adjoint in the original module-section universe. -/
instance compPushforward_isRightAdjoint
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PresheafOfModules.pushforward.{u}
      ((opensRingedSiteHom f ≫ opensRingedSiteHom g).structureSheafMap.hom)).IsRightAdjoint :=
  PresheafOfModules.SmallSourcePullback.isRightAdjoint
    (opensRingedSiteHom f ≫ opensRingedSiteHom g).structureSheafMap.hom

/-- Direct image along a composite of opens-ringed-site morphisms is additive. -/
instance compModulePushforward_additive
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedSite.Hom.modulePushforward (opensRingedSiteHom f ≫ opensRingedSiteHom g)).Additive := sorry

/-- Inverse image along a composite of opens-ringed-site morphisms is additive. -/
instance compModulePullback_additive
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedSite.Hom.modulePullback (opensRingedSiteHom f ≫ opensRingedSiteHom g)).Additive := sorry

end opensRingedSiteHom

end AlgebraicGeometry.RingedSpace
