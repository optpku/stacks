module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

@[expose] public section

/-!
# Derived categories of modules on ringed sites

This module builds the unbounded derived category from the ordinary module category, and owns the
homotopy-level functors whose total derived functors define derived pullback and pushforward along
a morphism of ringed sites.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The canonical standard derived-category structure on module sheaves over a ringed site. -/
@[reducible]
noncomputable def moduleCat_hasDerivedCategory.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)} (ModuleCat.{z} X) :=
  HasDerivedCategory.standard (ModuleCat.{z} X)

namespace RingPresentation

/-- The standard derived-category structure on a ring-sheaf presentation. -/
@[stacks 0FPB "ringed-site derived-category presentation", reducible]
noncomputable def moduleHasDerivedCategory.{z, u, v, w}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J RingCat.{w}) [UnivLE.{max u v, z}] :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)}
      (SheafOfModules.{z} O) :=
  moduleCat_hasDerivedCategory (RingedSite.ofRingSheaf J O)

end RingPresentation

namespace CommRingPresentation

/-- The standard derived-category structure on a commutative ring-sheaf presentation. -/
@[stacks 0FPB "commutative ringed-site derived-category presentation", reducible]
noncomputable def moduleHasDerivedCategory.{z, u, v, w}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w}) [UnivLE.{max u v, z}] :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)}
      (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)

end CommRingPresentation

/-- The unbounded derived category of module sheaves on a ringed site. -/
abbrev ModuleDerived.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :=
  @DerivedCategory.{max (max (max u v) w) (z + 1)}
    (ModuleCat.{z} X) inferInstance inferInstance (moduleCat_hasDerivedCategory X)

/-- The homotopy category of unbounded cochain complexes of module sheaves on a ringed site. -/
abbrev ModuleHomotopy.{z, u, v, w} (X : RingedSite.{u, v, w}) :=
  HomotopyCategory (ModuleCat.{z} X) (up ℤ)

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves. -/
abbrev ModuleQis.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :=
  HomotopyCategory.quasiIso (ModuleCat.{z} X) (up ℤ)

/-- The canonical localization from the homotopy category to the derived category of module
sheaves on a ringed site. -/
abbrev moduleLocalization.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :=
  @DerivedCategory.Qh.{max (max (max u v) w) (z + 1)}
    (ModuleCat.{z} X) inferInstance inferInstance (moduleCat_hasDerivedCategory X)

/-- The homotopy-to-derived functor induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y) [UnivLE.{max uY vY, z}] :
    ModuleHomotopy.{z} X ⥤ ModuleDerived.{z} Y :=
  (modulePushforward.{z} f).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization.{z} Y

section

universe z uX vX uY vY w

/-- A Grothendieck-abelian source gives the ringed-site direct image its canonical total right
derived functor.  This bridge exposes the generic K-injective instance through the
`modulePushforwardToDerived` presentation used by ringed-site APIs. -/
@[stacks 05TH]
theorem modulePushforwardToDerived.hasRightDerived
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X) := by
  exact @Functor.RightDerived.KInjective.hasDerived
    (ModuleCat.{z} X) inferInstance inferInstance
    (ModuleCat.{z} Y) inferInstance inferInstance (moduleCat_hasDerivedCategory.{z} Y)
    (modulePushforward.{z} f) inferInstance inferInstance

end

/-- The unbounded total right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)] :
    ModuleDerived.{z} X ⥤ ModuleDerived.{z} Y :=
  Functor.totalRightDerived (modulePushforwardToDerived.{z} f)
    (moduleLocalization.{z} X) (ModuleQis.{z} X)

/-- The homotopy-to-derived functor induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [(f.modulePushforward.{z}).IsRightAdjoint] :
    ModuleHomotopy.{z} Y ⥤ ModuleDerived.{z} X :=
  (modulePullback.{z} f).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization.{z} X

section

universe z uX vX uY vY w

/-- The generic `Functor.Homotopy.toDerived` spelling of module pullback has the same canonical
total-left-derived-functor witness as the homotopy-adjunction presentation. -/
theorem modulePullback.DerivedCategory.hasLeftDerived
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [hDerived : Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)] :
    Functor.HasLeftDerivedFunctor
      (@Functor.Homotopy.toDerived
        (ModuleCat.{z} Y) inferInstance inferInstance
        (ModuleCat.{z} X) inferInstance inferInstance (moduleCat_hasDerivedCategory X)
        (modulePullback.{z} f) inferInstance)
      (ModuleQis.{z} Y) := hDerived

end

/-- The unbounded total left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)] :
    ModuleDerived.{z} Y ⥤ ModuleDerived.{z} X :=
  Functor.totalLeftDerived (modulePullbackToDerived.{z} f)
    (moduleLocalization.{z} Y) (ModuleQis.{z} Y)

end RingedSite.Hom

/- The notation is scoped so ordinary ReasLib imports do not alter parsing globally.  It mirrors the
ringed-space derived-pushforward notation while pointing at the site-level canonical owner. -/
namespace RingedSiteDerived

/-- Notation for the total derived direct image on ringed-site modules. -/
scoped notation:max "R(" f ")_*" =>
  RingedSite.Hom.modulePushforwardDerived f

/-- Notation for the total derived inverse image on ringed-site modules. -/
scoped notation:max "L(" f ")^*" =>
  RingedSite.Hom.modulePullbackDerived f

end RingedSiteDerived
