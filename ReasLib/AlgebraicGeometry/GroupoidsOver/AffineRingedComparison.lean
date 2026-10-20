/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineRingedSite

/-!
# Affine comparison of associated ringed topoi

The special cocontinuous inclusion `𝒳_affine,τ ⟶ 𝒳_τ` induces a morphism of
ringed topoi `(Sh(𝒳_affine,τ), 𝒪) ⟶ (Sh(𝒳_τ), 𝒪_𝒳)`, where `𝒪` is the
restriction of the universe-lifted structure sheaf.  The ring-valued inverse
image differs from this restriction by the canonical
`CocontinuousPullback.comparison`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}


/-- The geometric morphism `Sh(𝒳_affine,τ) ⟶ Sh(𝒳_τ)` induced by the special
cocontinuous affine inclusion. -/
noncomputable def affineInclusionToTopos (X : GroupoidsOver S) (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (X.associatedTopology τ) (X.associatedAffineTopology τ) :=
  Functor.morphismOfTopoiInOfCocontinuous.{u + 1, u, u, u + 1, u + 1}
    (affineInclusion X) (X.associatedAffineTopology τ) (X.associatedTopology τ)

/-- The inverse image of `affineInclusionToTopos` is the cocontinuous sheaf
pullback. -/
theorem affineInclusionToTopos_inverseImage (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P] :
    (affineInclusionToTopos X τ).inverseImage =
      (affineInclusion X).sheafPullbackCocontinuous (Type (u + 1))
        (X.associatedAffineTopology τ) (X.associatedTopology τ) :=
  sorry

/-- The ring-valued comparison from the canonical inverse image of the lifted
`𝒪_𝒳` to the restriction `𝒪`, the mate of `CocontinuousPullback.comparison`. -/
noncomputable def associatedAffineStructureSheafComparison (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    (RingedSite.Cocontinuous.toTopos (affineInclusionRinged X τ)).ringInverseImage.obj
        (liftedAssociatedStructureSheaf X τ) ⟶
      associatedAffineStructureSheaf X τ :=
  RingedSite.Cocontinuous.structureMap (affineInclusionRinged X τ)
    (associatedAffineStructureSheafToPushforward X τ).inv

/-- `associatedAffineStructureSheafComparison` is the cocontinuous ring-valued
structure map induced by restriction. -/
theorem associatedAffineStructureSheafComparison_eq (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    associatedAffineStructureSheafComparison X τ =
      RingedSite.Cocontinuous.structureMap (affineInclusionRinged X τ)
        (associatedAffineStructureSheafToPushforward X τ).inv :=
  sorry

/-- The ring-valued comparison from inverse image to restriction is an
isomorphism. -/
instance associatedAffineStructureSheafComparison_isIso (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    IsIso (associatedAffineStructureSheafComparison X τ) :=
  sorry

/-- After forgetting to types, the ring-valued comparison is an isomorphism,
as required of the mate of `CocontinuousPullback.comparison`. -/
theorem associatedAffineStructureSheafComparison_forget (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    IsIso
      ((sheafCompose (X.associatedAffineTopology τ) (forget RingCat.{u + 1})).map
        (associatedAffineStructureSheafComparison X τ)) :=
  sorry

/-- The morphism of ringed topoi
`(Sh(𝒳_affine,τ), 𝒪) ⟶ (Sh(𝒳_τ), 𝒪_𝒳)` induced by the affine inclusion. -/
noncomputable def associatedAffineComparison (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    RingedSite.ToposHom (associatedAffineRingedSite X τ)
      (liftedAssociatedRingedSite X τ) where
  toTopos := RingedSite.Cocontinuous.toTopos (affineInclusionRinged X τ)
  structureMap := associatedAffineStructureSheafComparison X τ

/-- The underlying topos morphism of `associatedAffineComparison` is
`affineInclusionToTopos`. -/
theorem associatedAffineComparison_toTopos (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    (associatedAffineComparison X τ).toTopos = affineInclusionToTopos X τ :=
  sorry

/-- The structure map of `associatedAffineComparison` is the ring-valued
comparison from inverse image to restriction. -/
theorem associatedAffineComparison_structureMap (X : GroupoidsOver S)
    (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})] :
    (associatedAffineComparison X τ).structureMap =
      associatedAffineStructureSheafComparison X τ :=
  sorry

variable (X : GroupoidsOver S) (τ : StandardTopology)
variable [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
variable [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
    (affineInclusion X).op.HasPointwiseRightKanExtension P]
variable [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
variable [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})]

/-- The special cocontinuous inclusion of the associated affine site induces
an equivalence of ringed topoi, with the restricted lifted structure sheaf on
the affine site. -/
theorem associatedAffineComparison_isEquivalence :
    (associatedAffineComparison X τ).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
