/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived localization of modules on a commutative ringed site

The exact localization adjunction `j_! ⊣ j^*` descends to derived categories, together with
its canonical left- and right-adjoint consequences.
-/

@[expose] public section

-- Local instance justification (defeq pin): the result types of lowerShriekDerived and restrictionDerived must use the same commutative-ring-sheaf standard quotient explicitly passed to mapDerivedCategory in their bodies.
attribute [local instance] RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Localization

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [presheafRestrictionIsRightAdjoint :
  ((PresheafOfModules.pushforward
    (SheafOfModules.Localization.restrictionRingHom (ringSheaf J O) U).hom) :
      PresheafOfModules.{w} (ringSheaf J O).obj ⥤
        PresheafOfModules.{w} ((ringSheaf J O).over U).obj).IsRightAdjoint]
variable [HasSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction in the commutative ring-sheaf presentation inherits finite-limit preservation
from bundled localization of ringed sites. -/
@[stacks 08FJ "finite-limit preservation for derived localization"]
theorem restrictionPreservesFiniteLimits :
    PreservesFiniteLimits
      (restriction O U :
        ringedSiteModuleCategory.{u, v, w, w} J O ⥤
          ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) :=
  RingedSite.Hom.localizedRestriction_preservesFiniteLimits
    (RingedSite.ofCommRingSheaf J O) U

/-- Restriction in the commutative ring-sheaf presentation inherits finite-colimit preservation
from bundled localization of ringed sites. -/
@[stacks 08FJ "finite-colimit preservation for derived localization"]
theorem restrictionPreservesFiniteColimits :
    PreservesFiniteColimits
      (restriction O U :
        ringedSiteModuleCategory.{u, v, w, w} J O ⥤
          ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) :=
  RingedSite.Hom.localizedRestriction_preservesFiniteColimits
    (RingedSite.ofCommRingSheaf J O) U

/-- The explicit ringed-site presentation of extension by zero inherits the generic additive
structure of `SheafOfModules.Localization.lowerShriek`. -/
@[stacks 08FJ "additivity bridge for derived localization"]
theorem lowerShriekAdditive :
    (lowerShriek O U :
      ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U) ⥤
        ringedSiteModuleCategory.{u, v, w, w} J O).Additive :=
  SheafOfModules.Localization.lowerShriek.additive (ringSheaf J O) U

/-- The explicit ringed-site presentation of extension by zero preserves finite limits. -/
@[stacks 08FJ "finite-limit bridge for derived localization"]
theorem lowerShriekPreservesFiniteLimits :
    PreservesFiniteLimits
      (lowerShriek O U :
        ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U) ⥤
          ringedSiteModuleCategory.{u, v, w, w} J O) :=
  SheafOfModules.Localization.lowerShriek.preservesFiniteLimits (ringSheaf J O) U

/-- The explicit ringed-site presentation of extension by zero preserves finite colimits. -/
@[stacks 08FJ "finite-colimit bridge for derived localization"]
theorem lowerShriekPreservesFiniteColimits :
    PreservesFiniteColimits
      (lowerShriek O U :
        ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U) ⥤
          ringedSiteModuleCategory.{u, v, w, w} J O) :=
  SheafOfModules.Localization.lowerShriek.preservesFiniteColimits (ringSheaf J O) U

/-- The explicit ringed-site presentation of restriction inherits additivity from the canonical
pushforward along the localization ring morphism. -/
@[stacks 08FJ "additivity bridge for derived localization"]
theorem restrictionAdditive :
    (restriction O U :
      ringedSiteModuleCategory.{u, v, w, w} J O ⥤
        ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)).Additive :=
  SheafOfModules.pushforward_additive
    (SheafOfModules.Localization.restrictionRingHom (ringSheaf J O) U)

/-- Derived extension from the localization at `U`, with the module universe fixed by the
coefficient sheaf. -/
@[stacks 08FJ "derived lower shriek"]
noncomputable abbrev lowerShriekDerived :
    DerivedCategory
        (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  @CategoryTheory.Functor.mapDerivedCategory
    (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory (J.over U) (O.over U))
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory J O)
    (lowerShriek O U) (lowerShriekAdditive O U)
      (lowerShriekPreservesFiniteLimits O U) (lowerShriekPreservesFiniteColimits O U)

/-- Derived restriction from a commutative ringed site to its localization at `U`. -/
@[stacks 08FJ "derived restriction"]
noncomputable abbrev restrictionDerived :
    DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O) ⥤
      DerivedCategory
        (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) :=
  @CategoryTheory.Functor.mapDerivedCategory
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory J O)
    (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory (J.over U) (O.over U))
    (restriction O U) (restrictionAdditive O U)
      (restrictionPreservesFiniteLimits O U) (restrictionPreservesFiniteColimits O U)

/-- Derived extension from a localized ringed site is left adjoint to derived restriction. -/
@[stacks 08FJ]
noncomputable def derivedAdjunction :
    lowerShriekDerived O U ⊣ restrictionDerived O U :=
  @CategoryTheory.Adjunction.mapDerivedCategory
    (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory (J.over U) (O.over U))
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory J O)
    (lowerShriek O U) (restriction O U)
      (lowerShriekAdditive O U) (lowerShriekPreservesFiniteLimits O U)
      (lowerShriekPreservesFiniteColimits O U) (restrictionAdditive O U)
      (restrictionPreservesFiniteLimits O U) (restrictionPreservesFiniteColimits O U)
      (lowerShriekRestrictionAdj O U)

namespace lowerShriekDerived

/-- Derived extension from a localized commutative ringed site is a left adjoint. -/
@[stacks 08FJ "derived lower shriek is a left adjoint"]
theorem isLeftAdjoint :
    (lowerShriekDerived O U).IsLeftAdjoint :=
  (derivedAdjunction O U).isLeftAdjoint

end lowerShriekDerived

namespace restrictionDerived

/-- Derived restriction to a localized commutative ringed site is a right adjoint. -/
@[stacks 08FJ "derived restriction is a right adjoint"]
theorem isRightAdjoint :
    (restrictionDerived O U).IsRightAdjoint :=
  (derivedAdjunction O U).isRightAdjoint

end restrictionDerived

-- The adjunction data is produced by the generic exact-adjunction construction; its axiomatic
-- dependencies are confined to Prop-valued exactness and universal-property inputs.

end SheafOfModules.RingedSite.Localization
