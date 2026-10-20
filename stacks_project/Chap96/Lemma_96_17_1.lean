/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AbelianSheaf.Injective
public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 96.17.1: direct image along a morphism of categories fibred in groupoids
preserves injective abelian sheaves and injective modules for every standard topology. -/
@[stacks 06WX] #check (AlgebraicGeometry.GroupoidsOver.sheafPushforwardCocontinuous_preservesInjectiveObjects :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P],
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ)
        (Y.associatedTopology τ)).PreservesInjectiveObjects)

#check (AlgebraicGeometry.GroupoidsOver.injective_sheafPushforwardCocontinuous :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    (I : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) [Injective I],
    Injective
      (((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ)
          (Y.associatedTopology τ)).obj I))

#check (AlgebraicGeometry.GroupoidsOver.modulePushforward_preservesInjectiveObjects :
    ∀ {S : Scheme.{u}}
    (τ : StandardTopology)
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (StandardTopology.Big.liftedRingedSite τ S)}
    (f : X ⟶ Y)
    [HasSheafify (X.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
    [HasSheafify (Y.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1), X.p.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1), Y.p.op.HasPointwiseRightKanExtension P]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    [(τ.overTopology S).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.p.inheritedTopology (τ.overTopology S)).HasSheafCompose (forget RingCat.{u + 1})]
    [(Y.p.inheritedTopology (τ.overTopology S)).HasSheafCompose (forget RingCat.{u + 1})],
    ((toCartesianBasedFunctor f).inheritedToposHom.modulePushforward).PreservesInjectiveObjects)

#check (AlgebraicGeometry.GroupoidsOver.injective_modulePushforward :
    ∀ {S : Scheme.{u}}
    (τ : StandardTopology)
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (StandardTopology.Big.liftedRingedSite τ S)}
    (f : X ⟶ Y)
    [HasSheafify (X.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
    [HasSheafify (Y.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1), X.p.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1), Y.p.op.HasPointwiseRightKanExtension P]
    [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    [(τ.overTopology S).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.p.inheritedTopology (τ.overTopology S)).HasSheafCompose (forget RingCat.{u + 1})]
    [(Y.p.inheritedTopology (τ.overTopology S)).HasSheafCompose (forget RingCat.{u + 1})]
    (I : RingedSite.ModuleCat.{u + 1} X.p.inheritedRingedTopos) [Injective I],
    Injective ((toCartesianBasedFunctor f).inheritedToposHom.modulePushforward.obj I))
