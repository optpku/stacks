module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived projection formula for localization of module sheaves

For localization at `U`, derived extension by zero satisfies the projection formula against an
ambient derived module.  The restriction on the right-hand side is essential: this is not a
strong-monoidality assertion for `j_!`.
-/

@[expose] public section

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): the projection-formula types use the commutative-ring-sheaf module alias, while their derived functors already explicitly select this named standard quotient.
attribute [local instance] RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

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

namespace DerivedAdjunction

/-- Derived extension by zero from a localized ringed site satisfies the projection formula
against an ambient derived module. -/
@[stacks 0GL1]
theorem projectionFormula :
    @CategoryTheory.Adjunction.DerivedProjectionFormula
      (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) _ _ _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor (O.over U))
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor (O.over U)).right
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor O)
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor O).right
      _ _ (derivedAdjunction O U) := sorry

/-- The objectwise localization projection formula, exposed directly for downstream use. -/
@[stacks 0GL1 "objectwise localization projection formula"]
theorem isomorphic
    (L : DerivedCategory
      (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)))
    (K : DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O)) :
    IsIsomorphic
      (@DerivedCategory.DerivedTensor.Right.obj
        (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor O)
        ((lowerShriekDerived O U).obj L) K
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor O).right)
      ((lowerShriekDerived O U).obj
        (@DerivedCategory.DerivedTensor.Right.obj
          (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) _ _ _ _ _
          (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor (O.over U))
          L ((restrictionDerived O U).obj K)
          (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor (O.over U)).right)) := sorry

end DerivedAdjunction

end SheafOfModules.RingedSite.Localization
