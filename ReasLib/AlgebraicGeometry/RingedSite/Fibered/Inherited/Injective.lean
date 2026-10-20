module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Topos
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Adjunction.Abelian

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Direct image between the inherited ringed topoi of categories fibred in groupoids
preserves injective modules for every standard topology. -/
instance modulePushforward_preservesInjectiveObjects
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
    [(Y.p.inheritedTopology (τ.overTopology S)).HasSheafCompose (forget RingCat.{u + 1})] :
    ((toCartesianBasedFunctor f).inheritedToposHom.modulePushforward).PreservesInjectiveObjects :=
  sorry

/-- The direct image of an injective module between the inherited ringed topoi of
categories fibred in groupoids is injective for every standard topology. -/
theorem injective_modulePushforward
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
    (I : RingedSite.ModuleCat.{u + 1} X.p.inheritedRingedTopos) [Injective I] :
    Injective ((toCartesianBasedFunctor f).inheritedToposHom.modulePushforward.obj I) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
