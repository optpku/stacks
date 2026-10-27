/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedGlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.DerivedAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits

/-!
# Derived global sections for hypercoverings of an object

The canonical comparison on the localized ringed site is obtained from the
terminal-hypercovering comparison. Ambient derived modules enter through exact
derived restriction to the localized ringed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}] [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify
    (Localization.AtSimplicialSR.site (X := X.localization U)
      K.toSimplicialObject).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor
    (Localization.AtSimplicialSR.site (X := X.localization U)
      K.toSimplicialObject).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (X.localization U))]
variable [IsGrothendieckAbelian
    (RingedSite.ModuleCat.{w}
      (Localization.AtSimplicialSR.site (X := X.localization U) K.toSimplicialObject))]

/-- Leray identification of derived global sections after derived direct image
along the augmentation of a hypercovering of an object. -/
abbrev rGammaDirectImageIso :=
  Localization.AtSimplicialSR.rGammaDirectImageIso (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- The canonical comparison from derived global sections on the localized ringed
site to derived global sections after augmentation pullback. -/
abbrev rGammaPullbackComparison :=
  Localization.AtSimplicialSR.rGammaPullbackComparison (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- The canonical comparison is the derived unit, reassociated and postcomposed
with the Leray identification. -/
theorem rGammaPullbackComparison_eq :
    rGammaPullbackComparison U K =
      whiskerRight (derivedUnit U K)
          (Hom.moduleGlobalSectionsDerived.{w} (X.localization U)) ≫
        (associator (modulePullbackDerived U K) (modulePushforwardDerived U K)
            (Hom.moduleGlobalSectionsDerived.{w} (X.localization U))).hom ≫
        whiskerLeft (modulePullbackDerived U K) (rGammaDirectImageIso U K).hom := sorry

/-- The component of the canonical comparison is derived global sections of the
derived unit followed by the Leray identification. -/
theorem rGammaPullbackComparison_app
    (E : Hom.ModuleDerived.{w} (X.localization U)) :
    (rGammaPullbackComparison U K).app E =
      (Hom.moduleGlobalSectionsDerived.{w} (X.localization U)).map
          ((derivedUnit U K).app E) ≫
        (rGammaDirectImageIso U K).hom.app ((modulePullbackDerived U K).obj E) := sorry

/-- The canonical derived global-sections comparison for a hypercovering of an
object is invertible on the restriction of every unbounded ambient derived module. -/
@[instance] theorem rGammaPullbackComparison_restrict_app_isIso
    (E : Hom.ModuleDerived.{w} X) :
    IsIso ((rGammaPullbackComparison U K).app
      ((Hom.localizedRestrictionDerived.{w} X U).obj E)) := sorry

end RingedSite.Hypercovering
