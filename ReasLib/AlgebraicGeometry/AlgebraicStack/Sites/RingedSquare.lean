/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedMorphism

/-!
# Functoriality squares of lisse-étale and flat-fppf ringed topoi

A smooth (resp. flat) morphism of algebraic stacks fills a commutative square of
ringed topoi whose horizontal edges are the restricted-site inclusions and
whose vertical edges are the restricted and associated morphisms. The mixed
identities `f'_*(g')⁻¹ ≅ g⁻¹ f_*` and `g'_!(f')⁻¹ ≅ f⁻¹ g_!` are the
Beck-Chevalley isomorphism of that square and its left-adjoint mate.
The explicit existence hypotheses express the bounded-site size convention.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open RingedSite.ToposHom
open scoped Bicategory MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The site square `ι_X ≫ toFunctor f ≅ lisseEtaleMap f ≫ ι_Y` in the
`CatCommSq` packing used by Beck-Chevalley. -/
@[implicit_reducible]
def lisseEtaleBeckChevalleySquare (f : X ⟶ Y) [Smooth f] :
    CatCommSq (lisseEtaleInclusion X) (lisseEtaleMap f) (toFunctor f)
      (lisseEtaleInclusion Y) where
  iso := (lisseEtaleMap_comp_ι f).symm

/-- The stored isomorphism of `lisseEtaleBeckChevalleySquare` is
`(lisseEtaleMap_comp_ι f).symm`. -/
theorem lisseEtaleBeckChevalleySquare_iso (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleBeckChevalleySquare f).iso = (lisseEtaleMap_comp_ι f).symm :=
  sorry

/-- The canonical Sites comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` of the lisse-étale
functoriality square. -/
def lisseEtalePushforwardRestrictionComparison (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ⋙
      (lisseEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology Y) Y.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⋙
        (lisseEtaleMap f).sheafPushforwardCocontinuous (Type u)
          (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  CatCommSq.BeckChevalley.comparison.{u} (lisseEtaleTopology X) X.etaleTopology
    (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleBeckChevalleySquare f)

/-- `lisseEtalePushforwardRestrictionComparison` is the Beck-Chevalley
comparison of `lisseEtaleBeckChevalleySquare`. -/
theorem lisseEtalePushforwardRestrictionComparison_eq (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    lisseEtalePushforwardRestrictionComparison f =
      CatCommSq.BeckChevalley.comparison.{u} (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleBeckChevalleySquare f) :=
  sorry

/-- The canonical lisse-étale comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` is an
isomorphism. -/
instance lisseEtalePushforwardRestrictionComparison.instIsIso
    (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    IsIso (lisseEtalePushforwardRestrictionComparison f) :=
  sorry

/-- The mixed identity `f'_*(g')⁻¹ ≅ g⁻¹ f_*` of lisse-étale functoriality. -/
def lisseEtalePushforwardRestrictionIso (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⋙
      (lisseEtaleMap f).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ⋙
        (lisseEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology Y) Y.etaleTopology :=
  (asIso (lisseEtalePushforwardRestrictionComparison f)).symm

/-- `lisseEtalePushforwardRestrictionIso` is the inverse of the canonical
Beck-Chevalley comparison. -/
theorem lisseEtalePushforwardRestrictionIso_eq (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    lisseEtalePushforwardRestrictionIso f =
      (asIso (lisseEtalePushforwardRestrictionComparison f)).symm :=
  sorry

/-- Direct images around the lisse-étale functoriality square are canonically
isomorphic by composition of cocontinuous pushforwards. -/
def lisseEtaleFunctorialSquare_homIso (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (comp (lisseEtaleRingedToposHom X) (toFunctor.etaleRingedToposHom f)).toTopos.pushforward ≅
      (comp (lisseEtaleMap.ringedToposHom f) (lisseEtaleRingedToposHom Y)).toTopos.pushforward :=
  sheafPushforwardCocontinuousComp' (lisseEtaleTopology X) X.etaleTopology Y.etaleTopology
      (lisseEtaleInclusion X) (toFunctor f) (lisseEtaleMap_comp_ι f).symm ≪≫
    (sheafPushforwardCocontinuousComp (lisseEtaleTopology X) (lisseEtaleTopology Y)
      Y.etaleTopology (lisseEtaleMap f) (lisseEtaleInclusion Y)).symm

/-- `lisseEtaleFunctorialSquare_homIso` is the composite of the upper-right
comparison along `(lisseEtaleMap_comp_ι f).symm` with the inverse of the
composite-pushforward identification of `lisseEtaleMap f` and
`lisseEtaleInclusion Y`. -/
theorem lisseEtaleFunctorialSquare_homIso_eq (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    lisseEtaleFunctorialSquare_homIso f =
      sheafPushforwardCocontinuousComp' (lisseEtaleTopology X) X.etaleTopology
          Y.etaleTopology (lisseEtaleInclusion X) (toFunctor f)
          (lisseEtaleMap_comp_ι f).symm ≪≫
        (sheafPushforwardCocontinuousComp (lisseEtaleTopology X)
          (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleMap f)
          (lisseEtaleInclusion Y)).symm :=
  sorry

/-- Compatibility of `lisseEtaleFunctorialSquare_homIso` with ring-valued
direct-image structure maps. -/
theorem lisseEtaleFunctorialSquare_homIso_comm (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (comp (lisseEtaleRingedToposHom X)
          (toFunctor.etaleRingedToposHom f)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (lisseEtaleFunctorialSquare_homIso f).hom).app
          (lisseEtaleRingedSite X).structureSheaf =
      (comp (lisseEtaleMap.ringedToposHom f)
        (lisseEtaleRingedToposHom Y)).directStructureMap :=
  sorry

/-- The commutative square of ringed topoi for a smooth morphism of algebraic
stacks, with edges `g'`, `f'`, `f`, and `g`. -/
def lisseEtaleFunctorialSquare (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    CommSquare (lisseEtaleRingedSite X) (etaleRingedSite X)
      (lisseEtaleRingedSite Y) (etaleRingedSite Y) where
  upper := lisseEtaleRingedToposHom X
  left := lisseEtaleMap.ringedToposHom f
  right := toFunctor.etaleRingedToposHom f
  lower := lisseEtaleRingedToposHom Y
  cell :=
    { homIso := lisseEtaleFunctorialSquare_homIso f
      comm := lisseEtaleFunctorialSquare_homIso_comm f }

/-- The upper edge of `lisseEtaleFunctorialSquare` is the lisse-étale inclusion
of `X`. -/
theorem lisseEtaleFunctorialSquare_upper (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleFunctorialSquare f).upper = lisseEtaleRingedToposHom X :=
  sorry

/-- The left edge of `lisseEtaleFunctorialSquare` is the restricted morphism
`f'`. -/
theorem lisseEtaleFunctorialSquare_left (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleFunctorialSquare f).left = lisseEtaleMap.ringedToposHom f :=
  sorry

/-- The right edge of `lisseEtaleFunctorialSquare` is the associated-étale
morphism of `f`. -/
theorem lisseEtaleFunctorialSquare_right (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleFunctorialSquare f).right = toFunctor.etaleRingedToposHom f :=
  sorry

/-- The lower edge of `lisseEtaleFunctorialSquare` is the lisse-étale inclusion
of `Y`. -/
theorem lisseEtaleFunctorialSquare_lower (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleFunctorialSquare f).lower = lisseEtaleRingedToposHom Y :=
  sorry

/-- The stored `2`-cell of `lisseEtaleFunctorialSquare` is
`lisseEtaleFunctorialSquare_homIso`. -/
theorem lisseEtaleFunctorialSquare_homIso_eq_cell (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleFunctorialSquare f).cell.homIso =
      lisseEtaleFunctorialSquare_homIso f :=
  sorry

/-- The mixed identity `g'_!(f')⁻¹ ≅ f⁻¹ g_!` of lisse-étale functoriality, as
the left-adjoint mate of `lisseEtalePushforwardRestrictionIso`. -/
def lisseEtaleLowerShriekInverseImageIso (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify Y.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasLeftKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasLeftKanExtension P] :
    (lisseEtaleMap f).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ⋙
      lisseEtaleLowerShriek X ≅
      lisseEtaleLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          X.etaleTopology Y.etaleTopology :=
  Adjunction.leftAdjointUniq
    ((((lisseEtaleMap f).sheafPullbackCocontinuousAdjunction
            (lisseEtaleTopology X) (lisseEtaleTopology Y)).comp
        (lisseEtaleLowerShriek.adjunction X)).ofNatIsoRight
      (lisseEtalePushforwardRestrictionIso f))
    ((lisseEtaleLowerShriek.adjunction Y).comp
      ((toFunctor f).sheafPullbackCocontinuousAdjunction
        X.etaleTopology Y.etaleTopology))

/-- `lisseEtaleLowerShriekInverseImageIso` is the left-adjoint uniqueness
isomorphism of the two adjunctions identified by
`lisseEtalePushforwardRestrictionIso`. -/
theorem lisseEtaleLowerShriekInverseImageIso_eq (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify Y.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasLeftKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasLeftKanExtension P] :
    lisseEtaleLowerShriekInverseImageIso f =
      Adjunction.leftAdjointUniq
        ((((lisseEtaleMap f).sheafPullbackCocontinuousAdjunction
                (lisseEtaleTopology X) (lisseEtaleTopology Y)).comp
            (lisseEtaleLowerShriek.adjunction X)).ofNatIsoRight
          (lisseEtalePushforwardRestrictionIso f))
        ((lisseEtaleLowerShriek.adjunction Y).comp
          ((toFunctor f).sheafPullbackCocontinuousAdjunction
            X.etaleTopology Y.etaleTopology)) :=
  sorry

/-- The site square `ι_X ≫ toFunctor f ≅ flatFppfMap f ≫ ι_Y` in the
`CatCommSq` packing used by Beck-Chevalley. -/
@[implicit_reducible]
def flatFppfBeckChevalleySquare (f : X ⟶ Y) [Flat f] :
    CatCommSq (flatFppfInclusion X) (flatFppfMap f) (toFunctor f)
      (flatFppfInclusion Y) where
  iso := (flatFppfMap_comp_ι f).symm

/-- The stored isomorphism of `flatFppfBeckChevalleySquare` is
`(flatFppfMap_comp_ι f).symm`. -/
theorem flatFppfBeckChevalleySquare_iso (f : X ⟶ Y) [Flat f] :
    (flatFppfBeckChevalleySquare f).iso = (flatFppfMap_comp_ι f).symm :=
  sorry

/-- The canonical Sites comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` of the flat-fppf
functoriality square. -/
def flatFppfPushforwardRestrictionComparison (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
      (flatFppfInclusion Y).sheafPushforwardContinuous (Type u)
        (flatFppfTopology Y) (inheritedFppfTopology Y) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        (flatFppfMap f).sheafPushforwardCocontinuous (Type u)
          (flatFppfTopology X) (flatFppfTopology Y) :=
  CatCommSq.BeckChevalley.comparison.{u} (flatFppfTopology X) (inheritedFppfTopology X)
    (flatFppfTopology Y) (inheritedFppfTopology Y) (flatFppfBeckChevalleySquare f)

/-- `flatFppfPushforwardRestrictionComparison` is the Beck-Chevalley comparison
of `flatFppfBeckChevalleySquare`. -/
theorem flatFppfPushforwardRestrictionComparison_eq (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    flatFppfPushforwardRestrictionComparison f =
      CatCommSq.BeckChevalley.comparison.{u} (flatFppfTopology X)
        (inheritedFppfTopology X) (flatFppfTopology Y)
        (inheritedFppfTopology Y) (flatFppfBeckChevalleySquare f) :=
  sorry

/-- The canonical flat-fppf comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` is an
isomorphism. -/
instance flatFppfPushforwardRestrictionComparison.instIsIso
    (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    IsIso (flatFppfPushforwardRestrictionComparison f) :=
  sorry

/-- The mixed identity `f'_*(g')⁻¹ ≅ g⁻¹ f_*` of flat-fppf functoriality. -/
def flatFppfPushforwardRestrictionIso (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
      (flatFppfMap f).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
        (flatFppfInclusion Y).sheafPushforwardContinuous (Type u)
          (flatFppfTopology Y) (inheritedFppfTopology Y) :=
  (asIso (flatFppfPushforwardRestrictionComparison f)).symm

/-- `flatFppfPushforwardRestrictionIso` is the inverse of the canonical
Beck-Chevalley comparison. -/
theorem flatFppfPushforwardRestrictionIso_eq (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    flatFppfPushforwardRestrictionIso f =
      (asIso (flatFppfPushforwardRestrictionComparison f)).symm :=
  sorry

/-- Direct images around the flat-fppf functoriality square are canonically
isomorphic by composition of cocontinuous pushforwards. -/
def flatFppfFunctorialSquare_homIso (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (comp (flatFppfRingedToposHom X) (inheritedFppfRingedToposHom f)).toTopos.pushforward ≅
      (comp (flatFppfMap.ringedToposHom f) (flatFppfRingedToposHom Y)).toTopos.pushforward :=
  sheafPushforwardCocontinuousComp' (flatFppfTopology X) (inheritedFppfTopology X)
      (inheritedFppfTopology Y) (flatFppfInclusion X) (toFunctor f)
      (flatFppfMap_comp_ι f).symm ≪≫
    (sheafPushforwardCocontinuousComp (flatFppfTopology X) (flatFppfTopology Y)
      (inheritedFppfTopology Y) (flatFppfMap f) (flatFppfInclusion Y)).symm

/-- `flatFppfFunctorialSquare_homIso` is the composite of the upper-right
comparison along `(flatFppfMap_comp_ι f).symm` with the inverse of the
composite-pushforward identification of `flatFppfMap f` and
`flatFppfInclusion Y`. -/
theorem flatFppfFunctorialSquare_homIso_eq (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    flatFppfFunctorialSquare_homIso f =
      sheafPushforwardCocontinuousComp' (flatFppfTopology X)
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (flatFppfInclusion X) (toFunctor f) (flatFppfMap_comp_ι f).symm ≪≫
        (sheafPushforwardCocontinuousComp (flatFppfTopology X)
          (flatFppfTopology Y) (inheritedFppfTopology Y) (flatFppfMap f)
          (flatFppfInclusion Y)).symm :=
  sorry

/-- Compatibility of `flatFppfFunctorialSquare_homIso` with ring-valued
direct-image structure maps. -/
theorem flatFppfFunctorialSquare_homIso_comm (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (comp (flatFppfRingedToposHom X)
          (inheritedFppfRingedToposHom f)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (flatFppfFunctorialSquare_homIso f).hom).app
          (flatFppfRingedSite X).structureSheaf =
      (comp (flatFppfMap.ringedToposHom f)
        (flatFppfRingedToposHom Y)).directStructureMap :=
  sorry

/-- The commutative square of ringed topoi for a flat morphism of algebraic
stacks, with edges `g'`, `f'`, `f`, and `g`. -/
def flatFppfFunctorialSquare (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    CommSquare (flatFppfRingedSite X) (ringedSite X)
      (flatFppfRingedSite Y) (ringedSite Y) where
  upper := flatFppfRingedToposHom X
  left := flatFppfMap.ringedToposHom f
  right := inheritedFppfRingedToposHom f
  lower := flatFppfRingedToposHom Y
  cell :=
    { homIso := flatFppfFunctorialSquare_homIso f
      comm := flatFppfFunctorialSquare_homIso_comm f }

/-- The upper edge of `flatFppfFunctorialSquare` is the flat-fppf inclusion of
`X`. -/
theorem flatFppfFunctorialSquare_upper (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfFunctorialSquare f).upper = flatFppfRingedToposHom X :=
  sorry

/-- The left edge of `flatFppfFunctorialSquare` is the restricted morphism
`f'`. -/
theorem flatFppfFunctorialSquare_left (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfFunctorialSquare f).left = flatFppfMap.ringedToposHom f :=
  sorry

/-- The right edge of `flatFppfFunctorialSquare` is the inherited-fppf morphism
of `f`. -/
theorem flatFppfFunctorialSquare_right (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfFunctorialSquare f).right = inheritedFppfRingedToposHom f :=
  sorry

/-- The lower edge of `flatFppfFunctorialSquare` is the flat-fppf inclusion of
`Y`. -/
theorem flatFppfFunctorialSquare_lower (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfFunctorialSquare f).lower = flatFppfRingedToposHom Y :=
  sorry

/-- The stored `2`-cell of `flatFppfFunctorialSquare` is
`flatFppfFunctorialSquare_homIso`. -/
theorem flatFppfFunctorialSquare_homIso_eq_cell (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfFunctorialSquare f).cell.homIso =
      flatFppfFunctorialSquare_homIso f :=
  sorry

/-- The mixed identity `g'_!(f')⁻¹ ≅ f⁻¹ g_!` of flat-fppf functoriality, as
the left-adjoint mate of `flatFppfPushforwardRestrictionIso`. -/
def flatFppfLowerShriekInverseImageIso (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (inheritedFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasLeftKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasLeftKanExtension P] :
    (flatFppfMap f).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ⋙
      flatFppfLowerShriek X ≅
      flatFppfLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  Adjunction.leftAdjointUniq
    ((((flatFppfMap f).sheafPullbackCocontinuousAdjunction
            (flatFppfTopology X) (flatFppfTopology Y)).comp
        (flatFppfLowerShriek.adjunction X)).ofNatIsoRight
      (flatFppfPushforwardRestrictionIso f))
    ((flatFppfLowerShriek.adjunction Y).comp
      ((toFunctor f).sheafPullbackCocontinuousAdjunction
        (inheritedFppfTopology X) (inheritedFppfTopology Y)))

/-- `flatFppfLowerShriekInverseImageIso` is the left-adjoint uniqueness
isomorphism of the two adjunctions identified by
`flatFppfPushforwardRestrictionIso`. -/
theorem flatFppfLowerShriekInverseImageIso_eq (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (inheritedFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasLeftKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasLeftKanExtension P] :
    flatFppfLowerShriekInverseImageIso f =
      Adjunction.leftAdjointUniq
        ((((flatFppfMap f).sheafPullbackCocontinuousAdjunction
                (flatFppfTopology X) (flatFppfTopology Y)).comp
            (flatFppfLowerShriek.adjunction X)).ofNatIsoRight
          (flatFppfPushforwardRestrictionIso f))
        ((flatFppfLowerShriek.adjunction Y).comp
          ((toFunctor f).sheafPullbackCocontinuousAdjunction
            (inheritedFppfTopology X) (inheritedFppfTopology Y))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
