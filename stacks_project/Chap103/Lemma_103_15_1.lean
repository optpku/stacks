/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedSquare
import StacksCheckRecall

/-!
A smooth (resp. flat) morphism of algebraic stacks restricts to a continuous
and cocontinuous functor of lisse-étale (resp. flat-fppf) sites, inducing a
morphism of ringed topoi that fills a commutative square with the inclusions
of Lemma 103.14.2 and the associated-étale (resp. inherited-fppf) morphism,
and satisfying the mixed identities `f'_*(g')⁻¹ ≅ g⁻¹ f_*` and
`g'_!(f')⁻¹ ≅ f⁻¹ g_!`. The explicit existence hypotheses stand for
the Stacks bounded-site size convention.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open RingedSite.ToposHom
open scoped Bicategory MorphismOfTopoiIn

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)

section Smooth

variable [Smooth f]

/- Lemma 103.15.1 (1): a smooth morphism of algebraic stacks restricts to a
functor X_lisse,étale ⟶ Y_lisse,étale. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap :
  ∀ (f : X ⟶ Y) [Smooth f], lisseEtaleSite X ⥤ lisseEtaleSite Y)

/- Lemma 103.15.1 (2): the restricted lisse-étale functor is continuous. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.instIsContinuous :
  ∀ (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f).IsContinuous (lisseEtaleTopology X) (lisseEtaleTopology Y))

/- Lemma 103.15.1 (3): the restricted lisse-étale functor is cocontinuous. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.instIsCocontinuous :
  ∀ (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f).IsCocontinuous (lisseEtaleTopology X) (lisseEtaleTopology Y))

/- Lemma 103.15.1 (4): the restricted functor gives a morphism of ringed topoi
f' : Sh(X_lisse,étale) ⟶ Sh(Y_lisse,étale). -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.ringedToposHom :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (lisseEtaleRingedSite X) (lisseEtaleRingedSite Y))

/- Lemma 103.15.1 (5): f' fills a commutative square with the lisse-étale
inclusions g', g and the associated-étale morphism f. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare :
  ∀ (f : X ⟶ Y) [Smooth f]
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
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    CommSquare (lisseEtaleRingedSite X) (etaleRingedSite X)
      (lisseEtaleRingedSite Y) (etaleRingedSite Y))

/- Lemma 103.15.1 (6): f'_*(g')⁻¹ ≅ g⁻¹ f_* on sheaves of types. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⋙
      (lisseEtaleMap f).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ⋙
        (lisseEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology Y) Y.etaleTopology)

/- Lemma 103.15.1 (7): g'_!(f')⁻¹ ≅ f⁻¹ g_! on sheaves of types. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriekInverseImageIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify Y.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasLeftKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasLeftKanExtension P],
    (lisseEtaleMap f).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ⋙
      lisseEtaleLowerShriek X ≅
      lisseEtaleLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          X.etaleTopology Y.etaleTopology)

end Smooth

section Flat

variable [Flat f]

/- Lemma 103.15.1 (8): a flat morphism of algebraic stacks restricts to a
functor X_flat,fppf ⟶ Y_flat,fppf. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap :
  ∀ (f : X ⟶ Y) [Flat f], flatFppfSite X ⥤ flatFppfSite Y)

/- Lemma 103.15.1 (9): the restricted flat-fppf functor is continuous. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.instIsContinuous :
  ∀ (f : X ⟶ Y) [Flat f],
    (flatFppfMap f).IsContinuous (flatFppfTopology X) (flatFppfTopology Y))

/- Lemma 103.15.1 (10): the restricted flat-fppf functor is cocontinuous. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.instIsCocontinuous :
  ∀ (f : X ⟶ Y) [Flat f],
    (flatFppfMap f).IsCocontinuous (flatFppfTopology X) (flatFppfTopology Y))

/- Lemma 103.15.1 (11): the restricted functor gives a morphism of ringed topoi
f' : Sh(X_flat,fppf) ⟶ Sh(Y_flat,fppf). -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.ringedToposHom :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (flatFppfRingedSite X) (flatFppfRingedSite Y))

/- Lemma 103.15.1 (12): f' fills a commutative square with the flat-fppf
inclusions g', g and the inherited-fppf morphism f. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare :
  ∀ (f : X ⟶ Y) [Flat f]
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
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    CommSquare (flatFppfRingedSite X) (ringedSite X)
      (flatFppfRingedSite Y) (ringedSite Y))

/- Lemma 103.15.1 (13): f'_*(g')⁻¹ ≅ g⁻¹ f_* on sheaves of types. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
      (flatFppfMap f).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
        (flatFppfInclusion Y).sheafPushforwardContinuous (Type u)
          (flatFppfTopology Y) (inheritedFppfTopology Y))

/- Lemma 103.15.1 (14): g'_!(f')⁻¹ ≅ f⁻¹ g_! on sheaves of types. -/
@[stacks 07AT]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriekInverseImageIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (inheritedFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasLeftKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasLeftKanExtension P],
    (flatFppfMap f).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ⋙
      flatFppfLowerShriek X ≅
      flatFppfLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          (inheritedFppfTopology X) (inheritedFppfTopology Y))

end Flat
