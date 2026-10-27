/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.Sites.Hypercovering.Slice
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedAdjunction

/-!
# Derived module adjunction for hypercoverings of an object
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
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

/-- The unbounded derived inverse image of module sheaves along the augmentation
of a hypercovering of an object. -/
abbrev modulePullbackDerived :
    Hom.ModuleDerived.{w} (X.localization U) ⥤
      Hom.ModuleDerived.{w}
        (Localization.AtSimplicialSR.site (X := X.localization U) K.toSimplicialObject) :=
  Localization.AtSimplicialSR.derivedPullback (X := X.localization U)
    (toSliceTerminal X.siteTopology U K).simplicial

/-- The unbounded derived direct image of module sheaves along the augmentation
of a hypercovering of an object. -/
abbrev modulePushforwardDerived :
    Hom.ModuleDerived.{w}
        (Localization.AtSimplicialSR.site (X := X.localization U) K.toSimplicialObject) ⥤
      Hom.ModuleDerived.{w} (X.localization U) :=
  Localization.AtSimplicialSR.derivedPushforward (X := X.localization U)
    (toSliceTerminal X.siteTopology U K).simplicial

/-- The canonical adjunction between unbounded derived inverse and direct image
of module sheaves along a hypercovering of an object. -/
abbrev moduleDerivedAdjunction :
    modulePullbackDerived U K ⊣ modulePushforwardDerived U K :=
  Localization.AtSimplicialSR.derivedAdjunction (X := X.localization U)
    (toSliceTerminal X.siteTopology U K).simplicial

/-- The canonical derived module unit on the localized ringed site of an object
with respect to a hypercovering. -/
abbrev derivedUnit :
    𝟭 (Hom.ModuleDerived.{w} (X.localization U)) ⟶
      modulePullbackDerived U K ⋙ modulePushforwardDerived U K :=
  Localization.AtSimplicialSR.derivedUnit (X := X.localization U)
    (toSliceTerminal X.siteTopology U K)

end RingedSite.Hypercovering
