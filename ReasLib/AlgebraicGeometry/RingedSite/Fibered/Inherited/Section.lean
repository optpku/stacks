/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.AmbientSquare
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Action
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Sections of localized inherited projections

For a fibred category with its inherited topology, the projection on a slice
has a section induced by cartesian pullback.  A morphism of fibred categories
preserves these sections.  This file records the resulting topos-level
statements without depending on a chapter-specific presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace CategoryTheory.FiberedCategoryOver.LocalizedSection

variable {D : RingedSite.{u, v}}

section Projection

variable (P : FiberedCategoryOver.{u, v, u, v} D.carrier) (U : P.total)
variable [IsMorphismOfSites (P.p.inheritedTopology D.siteTopology) D.siteTopology P.p]
variable [HasWeakSheafify (D.siteTopology.over (P.p.obj U)) (Type (max u v))]
variable [∀ Q : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.post P.p).op.HasLeftKanExtension Q]
variable [PreservesFiniteLimits
  ((Over.post P.p).sheafPullback
    (Type (max u v))
    ((P.p.inheritedTopology D.siteTopology).over U)
    (D.siteTopology.over (P.p.obj U)))]

/-- The localized projection morphism of topoi for an object of a fibred category. -/
@[stacks 08P9 "localized inherited projection"]
noncomputable def projection : MorphismOfTopoiIn
    ((P.p.inheritedRingedSite.localization U).siteTopology)
    ((D.localization (P.p.obj U)).siteTopology) :=
  ((P.p.inheritedProjectionRingedSiteHom).localization U).toMorphismOfTopoi

/-- The source-level certificate for a section of the localized projection. -/
@[stacks 08P9 "localized projection section predicate"]
def IsSection
    (σ : MorphismOfTopoiIn
      ((D.localization (P.p.obj U)).siteTopology)
      ((P.p.inheritedRingedSite.localization U).siteTopology)) : Prop :=
  MorphismOfTopoiIn.comp σ (projection P U) =
      MorphismOfTopoiIn.id ((D.localization (P.p.obj U)).siteTopology) ∧
    σ⁻¹ = projection P U _*

/-- The retraction component of a localized projection section. -/
@[stacks 08P9 "localized projection section retraction"]
theorem IsSection.projection_comp
    {σ : MorphismOfTopoiIn
      ((D.localization (P.p.obj U)).siteTopology)
      ((P.p.inheritedRingedSite.localization U).siteTopology)}
    (hσ : IsSection P U σ) :
    MorphismOfTopoiIn.comp σ (projection P U) =
      MorphismOfTopoiIn.id ((D.localization (P.p.obj U)).siteTopology) := sorry

/-- The inverse-image component of a localized projection section. -/
@[stacks 08P9 "localized projection section inverse image"]
theorem IsSection.inverseImage_eq_projectionPushforward
    {σ : MorphismOfTopoiIn
      ((D.localization (P.p.obj U)).siteTopology)
      ((P.p.inheritedRingedSite.localization U).siteTopology)}
    (hσ : IsSection P U σ) :
    σ⁻¹ = projection P U _* := sorry

/-- Lemma 21.38.2 (08P9): the localized projection of an inherited site has a
section whose inverse image is the projection direct image. -/
@[stacks 08P9]
theorem projection_exists :
    ∃ σ : MorphismOfTopoiIn
        ((D.localization (P.p.obj U)).siteTopology)
        ((P.p.inheritedRingedSite.localization U).siteTopology),
      IsSection P U σ := sorry

end Projection

section Comparison

variable {C C' : FiberedCategoryOver.{u, v, u, v} D.carrier}
variable (f : C' ⟶ C) (U' : C'.total)
variable [IsMorphismOfSites (C'.p.inheritedTopology D.siteTopology) D.siteTopology C'.p]
variable [IsMorphismOfSites (C.p.inheritedTopology D.siteTopology) D.siteTopology C.p]
variable [HasWeakSheafify (D.siteTopology.over (C'.p.obj U')) (Type (max u v))]
variable [IsMorphismOfSites
  (C'.p.inheritedTopology D.siteTopology)
  (C.p.inheritedTopology D.siteTopology)
  (FiberedCategoryOver.toFunctor f)]
variable [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
  (Over.post C'.p).op.HasLeftKanExtension Q]
variable [∀ Q : (Over ((FiberedCategoryOver.toFunctor f).obj U'))ᵒᵖ ⥤ Type (max u v),
  (Over.post C.p).op.HasLeftKanExtension Q]
variable [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
  (Over.post (FiberedCategoryOver.toFunctor f)).op.HasLeftKanExtension Q]
variable [PreservesFiniteLimits
  ((Over.post C'.p).sheafPullback
    (Type (max u v))
    ((C'.p.inheritedTopology D.siteTopology).over U')
    (D.siteTopology.over (C'.p.obj U')))]
variable [PreservesFiniteLimits
  ((Over.post C.p).sheafPullback
    (Type (max u v))
    ((C.p.inheritedTopology D.siteTopology).over ((FiberedCategoryOver.toFunctor f).obj U'))
    (D.siteTopology.over (C.p.obj ((FiberedCategoryOver.toFunctor f).obj U'))))]
variable [PreservesFiniteLimits
  ((Over.post (FiberedCategoryOver.toFunctor f)).sheafPullback
    (Type (max u v))
    ((C'.p.inheritedTopology D.siteTopology).over U')
    ((C.p.inheritedTopology D.siteTopology).over ((FiberedCategoryOver.toFunctor f).obj U')))]

/-- The localized morphism of inherited topoi induced by a morphism of fibred categories. -/
@[stacks 08PB "localized inherited comparison"]
noncomputable def comparison : MorphismOfTopoiIn
    ((C'.p.inheritedRingedSite.localization U').siteTopology)
    ((C.p.inheritedRingedSite.localization ((FiberedCategoryOver.toFunctor f).obj U')).siteTopology) :=
  ((Functor.inheritedRingedSiteHom (p := C.p) (p' := C'.p)
    (FiberedCategoryOver.toFunctor f) (FiberedCategoryOver.comm f)).localization U').toMorphismOfTopoi

/-- Transport between the two localizations of the base identified by projection compatibility. -/
@[stacks 08PB "base relocalization"]
noncomputable def baseRelocalization : MorphismOfTopoiIn
    ((D.localization (C.p.obj ((FiberedCategoryOver.toFunctor f).obj U'))).siteTopology)
    ((D.localization (C'.p.obj U')).siteTopology) :=
  (RingedSite.Localization.relocalization D
    (eqToHom (Functor.inheritedRingedSiteHom.projection_obj
      (FiberedCategoryOver.toFunctor f) (FiberedCategoryOver.comm f) U').symm)).toTopos

/-- The section at the target induced by a compatible section at the source. -/
@[stacks 08PB "induced target section"]
noncomputable def targetSection
    (σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)) :
    MorphismOfTopoiIn
      ((D.localization (C.p.obj ((FiberedCategoryOver.toFunctor f).obj U'))).siteTopology)
      ((C.p.inheritedRingedSite.localization ((FiberedCategoryOver.toFunctor f).obj U')).siteTopology) :=
  MorphismOfTopoiIn.comp (baseRelocalization f U')
    (MorphismOfTopoiIn.comp σ' (comparison f U'))

/-- The four source conditions for a localized section and its induced target section. Keeping this
predicate named makes the retraction and inverse-image data reusable without exposing a positional
conjunction as the primary API. -/
@[stacks 08PB "localized section compatibility predicate"]
def IsCompatible
    (σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)) : Prop :=
  MorphismOfTopoiIn.comp σ' (projection C' U') =
      MorphismOfTopoiIn.id ((D.localization (C'.p.obj U')).siteTopology) ∧
    MorphismOfTopoiIn.comp (targetSection f U' σ')
        (projection C ((FiberedCategoryOver.toFunctor f).obj U')) =
      MorphismOfTopoiIn.id
        ((D.localization (C.p.obj ((FiberedCategoryOver.toFunctor f).obj U'))).siteTopology) ∧
    σ'⁻¹ = projection C' U' _* ∧
    (targetSection f U' σ')⁻¹ =
      projection C ((FiberedCategoryOver.toFunctor f).obj U') _*

/-- The localized source section is a right inverse to the source projection. -/
@[stacks 08PB "source section retraction"]
theorem IsCompatible.projection_comp
    {σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)}
    (hσ : IsCompatible f U' σ') :
    MorphismOfTopoiIn.comp σ' (projection C' U') =
      MorphismOfTopoiIn.id ((D.localization (C'.p.obj U')).siteTopology) := sorry

/-- The induced target section is a right inverse to the target projection. -/
@[stacks 08PB "target section retraction"]
theorem IsCompatible.target_projection_comp
    {σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)}
    (hσ : IsCompatible f U' σ') :
    MorphismOfTopoiIn.comp (targetSection f U' σ')
        (projection C ((FiberedCategoryOver.toFunctor f).obj U')) =
    MorphismOfTopoiIn.id
        ((D.localization (C.p.obj ((FiberedCategoryOver.toFunctor f).obj U'))).siteTopology) := sorry

/-- The inverse image of a compatible source section is the canonical projection pushforward. -/
@[stacks 08PB "source section inverse image"]
theorem IsCompatible.inverseImage_eq_projectionPushforward
    {σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)}
    (hσ : IsCompatible f U' σ') :
    σ'⁻¹ = projection C' U' _* := sorry

/-- The inverse image of the induced target section is the target projection pushforward. -/
@[stacks 08PB "target section inverse image"]
theorem IsCompatible.targetInverseImage_eq_projectionPushforward
    {σ' : MorphismOfTopoiIn
      ((D.localization (C'.p.obj U')).siteTopology)
      ((C'.p.inheritedRingedSite.localization U').siteTopology)}
    (hσ : IsCompatible f U' σ') :
    (targetSection f U' σ')⁻¹ =
      projection C ((FiberedCategoryOver.toFunctor f).obj U') _* := sorry

/-- Lemma 21.38.4 (08PB): the localized section attached to the source of a
morphism of fibred categories also gives the compatible localized section at
its target. -/
@[stacks 08PB]
theorem comparison_exists :
    ∃ σ' : MorphismOfTopoiIn
        ((D.localization (C'.p.obj U')).siteTopology)
        ((C'.p.inheritedRingedSite.localization U').siteTopology),
      IsCompatible f U' σ' := sorry

end Comparison

-- Any `sorryAx` below is inherited through Prop-valued site, localization, or naturality laws;
-- the four displayed morphisms themselves are given by the canonical constructions above.

end CategoryTheory.FiberedCategoryOver.LocalizedSection
