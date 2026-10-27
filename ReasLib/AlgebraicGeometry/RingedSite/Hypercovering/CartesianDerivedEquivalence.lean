/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.ModuleDescent
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.CartesianDerivedEquivalence

/-!
# Bounded-below cartesian derived equivalence of an object hypercovering

Derived augmentation pullback identifies bounded-below modules on a localized
ringed site with bounded-below modules having cartesian cohomology on the total
site of a hypercovering. Derived augmentation pushforward is its quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `La^*`/`Ra_*` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [HasWeakSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K.toSimplicialObject) (op n)).op.HasPointwiseRightKanExtension
        P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.toSimplicialObject.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology (X.localization U).siteTopology
      (K.toSimplicialObject.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [toAmbientRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageInclRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageMapRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [ToposHom.HasModulePullbackDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModulePushforwardDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModuleDerivedAdjunction
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]

/-- The bounded-below cohomology property cut out by cartesian modules on the
ringed total site of a hypercovering of `U`. -/
abbrev cartesianPlusProperty :=
  Localization.AtSimplicialSR.cartesianPlusProperty (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- The full subcategory of bounded-below derived modules with cartesian
cohomology on the ringed total site of a hypercovering of `U`. -/
abbrev CartesianPlus :=
  Localization.AtSimplicialSR.CartesianPlus (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- Derived augmentation pullback from the localized ringed site, corestricted
to bounded-below derived modules with cartesian cohomology. -/
abbrev plusCartesianFunctor :=
  Localization.AtSimplicialSR.plusCartesianFunctor (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- Derived augmentation pushforward to the localized ringed site, restricted
to bounded-below derived modules with cartesian cohomology. -/
abbrev plusCartesianInverse :=
  Localization.AtSimplicialSR.plusCartesianInverse (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- Derived augmentation pullback identifies bounded-below modules on the
localized ringed site with bounded-below total-site modules having cartesian
cohomology, with quasi-inverse given by derived augmentation pushforward. -/
def modulePlusCartesianEquivalence :
    DerivedCategory.Plus (ModuleCat.{w} (X.localization U)) ≌ CartesianPlus U K :=
  Localization.AtSimplicialSR.plusCartesianEquivalence (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- Cartesian modules on the ringed total site of an object hypercovering form
a weak Serre subcategory. -/
instance cartesianProperty_isWeakSerreClass :
    CategoryTheory.ObjectProperty.IsWeakSerreClass
      (Localization.AtSimplicialSR.cartesianProperty (X := X.localization U)
        (toSliceTerminal X.siteTopology U K).simplicial) :=
  Localization.AtSimplicialSR.cartesianProperty_isWeakSerreClass (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- The forward functor of the cartesian derived equivalence is derived
augmentation pullback corestricted to cartesian cohomology. -/
theorem modulePlusCartesianEquivalence_functor :
    (modulePlusCartesianEquivalence U K).functor = plusCartesianFunctor U K := sorry

/-- The inverse functor of the cartesian derived equivalence is derived
augmentation pushforward restricted to cartesian cohomology. -/
theorem modulePlusCartesianEquivalence_inverse :
    (modulePlusCartesianEquivalence U K).inverse = plusCartesianInverse U K := sorry

/-- Derived augmentation pullback corestricted to bounded-below derived modules
with cartesian cohomology is an equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor U K).IsEquivalence :=
  Equivalence.isEquivalence_functor (modulePlusCartesianEquivalence U K)

end RingedSite.Hypercovering
