/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RepresentablePushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits Opposite
open FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u w

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (hf : relativelyRepresentable f) (τ : StandardTopology)

/- Lemma 96.5.3: the representing functor of a representable morphism defines a
morphism of associated sites, is continuous, and induces the same morphism of
topoi; presheaf pushforward is evaluation at the representing object. -/
@[stacks 06W8] #check
  (CategoryTheory.Functor.ContinuousRightAdjoint.right_isMorphismOfSites
    (toFunctor f) (AlgebraicGeometry.GroupoidsOver.representingFunctor f hf)
    (CategoryTheory.FiberedCategoryOver.Groupoids.representingFunctor.adjunction f
      (relativelyRepresentable.targetYoneda hf)) :
    IsMorphismOfSites (Y.associatedTopology τ) (X.associatedTopology τ)
      (AlgebraicGeometry.GroupoidsOver.representingFunctor f hf))

#check (AlgebraicGeometry.GroupoidsOver.representingFunctor_isContinuous f hf τ :
  (AlgebraicGeometry.GroupoidsOver.representingFunctor f hf).IsContinuous
    (Y.associatedTopology τ) (X.associatedTopology τ))

section morphismOfTopoiIn

variable [HasSheafify (X.associatedTopology τ) (Type (max (u + 1) w))]
variable [∀ P : X.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (AlgebraicGeometry.GroupoidsOver.representingFunctor f hf).op.HasLeftKanExtension P]

#check (AlgebraicGeometry.GroupoidsOver.representingFunctor_inverseImageIso f hf τ :
  ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).inverseImage ≅
    (AlgebraicGeometry.GroupoidsOver.representingFunctor_morphismOfTopoiIn f hf τ).inverseImage)

#check (AlgebraicGeometry.GroupoidsOver.representingFunctor_pushforwardIso f hf τ :
  ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).pushforward ≅
    (AlgebraicGeometry.GroupoidsOver.representingFunctor_morphismOfTopoiIn f hf τ).pushforward)

end morphismOfTopoiIn

variable [∀ P : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op P]
variable (F : X.totalᵒᵖ ⥤ Type w) (y : Y.total)

#check (AlgebraicGeometry.GroupoidsOver.representingFunctor_pushforward_obj f hf F y :
  IsIso (CategoryTheory.FiberedCategoryOver.Groupoids.representingFunctor.pushforwardComparison
    f (relativelyRepresentable.targetYoneda hf) F y))
