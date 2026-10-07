module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Topos
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology

/-!
# Pushforward of injective sheaves on categories fibred in groupoids

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has exact
inverse image, so its associated direct image preserves injective objects on
abelian sheaves and on modules for every standard topology `τ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 96.17.1 (1): the abelian sheaf pushforward `f_*` associated to a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` preserves
injective objects of `Ab(X_τ)` for every standard topology `τ`. -/
@[stacks 06WX, instance]
instance sheafPushforwardCocontinuous_preservesInjectiveObjects
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ)
        (Y.associatedTopology τ)).PreservesInjectiveObjects :=
  sorry

/-- Objectwise form of abelian sheaf pushforward preserving injectives. -/
theorem injective_sheafPushforwardCocontinuous
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    (I : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective
      (((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ)
          (Y.associatedTopology τ)).obj I) :=
  sorry

/-- Groupoid fibrations over the universe-lifted big `τ`-ringed site of `S` are
the objects of `GroupoidsOver S`, because that ringed site has underlying
category `Over S`. -/
theorem groupoidsOver_liftedRingedSite (τ : StandardTopology) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
        (StandardTopology.Big.liftedRingedSite τ S) =
      GroupoidsOver S :=
  sorry

/-- Lemma 96.17.1 (2): the module pushforward `f_*` associated to a 1-morphism
of categories fibred in groupoids over `(Sch/S)_fppf` preserves injective
objects of `Mod(X_τ, O_X)` for every standard topology `τ`. -/
@[stacks 06WX, instance]
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

/-- Objectwise form of module pushforward preserving injectives. -/
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
