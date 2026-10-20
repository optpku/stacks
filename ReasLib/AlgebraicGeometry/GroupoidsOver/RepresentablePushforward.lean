/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.RepresentingFunctor

/-!
# Continuity of the representing functor of a representable 1-morphism

A representable 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` has a representing functor `u : Y_τ ⥤ X_τ` which is
continuous, defines a morphism of sites `X_τ → Y_τ`, and induces the same
morphism of topoi as `f` itself. Pushforward along `f` evaluates as
`F(u(y))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits Opposite
open FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.representingFunctor
  (structureMap adjunction pushforwardComparison)
open Functor.LeftAdjoint Functor.ContinuousRightAdjoint
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (hf : relativelyRepresentable f) (τ : StandardTopology)

/-- The representing functor `u : Y.total ⥤ X.total` of a relatively
representable 1-morphism `f : X ⟶ Y`, sending each `y` to a chosen
representing object of `x ↦ ((toFunctor f).obj x ⟶ y)`. -/
noncomputable abbrev representingFunctor (f : X ⟶ Y)
    (hf : relativelyRepresentable f) : Y.total ⥤ X.total :=
  FiberedCategoryOver.Groupoids.representingFunctor f
    (relativelyRepresentable.targetYoneda hf)

/-- For a morphism `β : y' ⟶ y` in `Y`, the square of structure morphisms
`p(u(β))` along `q(β)` is a fibre product. -/
theorem representingFunctor_structureMap_isPullback {y' y : Y.total}
    (β : y' ⟶ y) :
    IsPullback (X.p.map ((representingFunctor f hf).map β))
      (structureMap f (relativelyRepresentable.targetYoneda hf) y')
      (structureMap f (relativelyRepresentable.targetYoneda hf) y)
      (Y.p.map β) :=
  sorry

/-- The representing functor preserves `τ`-covering families. -/
theorem representingFunctor_coverPreserving :
    CoverPreserving (Y.associatedTopology τ) (X.associatedTopology τ)
      (representingFunctor f hf) :=
  sorry

/-- The representing functor is continuous for each standard associated topology. -/
instance representingFunctor_isContinuous :
    (representingFunctor f hf).IsContinuous
      (Y.associatedTopology τ) (X.associatedTopology τ) :=
  (@Functor.isContinuous_iff_coverPreserving _ _ _ _ (representingFunctor f hf)
    (Y.associatedTopology τ) (X.associatedTopology τ)
    (RepresentablyFlat.of_isRightAdjoint (representingFunctor f hf))).2
    (representingFunctor_coverPreserving f hf τ)

/-- Cocontinuity of `toFunctor f` on associated `τ`-topologies is the
inherited-topology cocontinuity of `toCartesianBasedFunctor f`. -/
instance toFunctor_isCocontinuous :
    (toFunctor f).IsCocontinuous (X.associatedTopology τ) (Y.associatedTopology τ) :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (τ.overTopology S)

section morphismOfTopoiIn

variable [HasSheafify (X.associatedTopology τ) (Type (max (u + 1) w))]
variable [∀ P : X.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (representingFunctor f hf).op.HasLeftKanExtension P]

/-- Sheaf pullback along the representing functor preserves finite limits. -/
instance representingFunctor_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((representingFunctor f hf).sheafPullback (Type (max (u + 1) w))
        (Y.associatedTopology τ) (X.associatedTopology τ)) :=
  (Functor.LeftAdjoint.pullbackExact (representingFunctor f hf) (toFunctor f)
    (adjunction f (relativelyRepresentable.targetYoneda hf))).1

/-- The morphism of topoi `Sh(X_τ) ⟶ Sh(Y_τ)` presented by the continuous
representing functor `u : Y_τ → X_τ`. -/
noncomputable def representingFunctor_morphismOfTopoiIn :
    MorphismOfTopoiIn (Y.associatedTopology τ) (X.associatedTopology τ) :=
  (representingFunctor f hf).morphismOfTopoiInOfContinuous
    (Y.associatedTopology τ) (X.associatedTopology τ)

/-- The inverse image induced by the total functor is canonically isomorphic to
sheaf pullback along the representing functor. -/
noncomputable def representingFunctor_inverseImageIso :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).inverseImage ≅
      (representingFunctor_morphismOfTopoiIn f hf τ).inverseImage :=
  pullbackCocontinuousIsoConstruction (representingFunctor f hf) (toFunctor f)
      (adjunction f (relativelyRepresentable.targetYoneda hf))
      (Type (max (u + 1) w)) ≪≫
    (sheafPullbackConstruction.sheafPullbackIso (representingFunctor f hf)
      (Type (max (u + 1) w)) (Y.associatedTopology τ)
      (X.associatedTopology τ)).symm

/-- The direct image induced by the total functor is canonically isomorphic to
continuous direct image along the representing functor. -/
noncomputable def representingFunctor_pushforwardIso :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).pushforward ≅
      (representingFunctor_morphismOfTopoiIn f hf τ).pushforward :=
  (pushforwardContinuousIso (toFunctor f) (representingFunctor f hf)
      (Type (max (u + 1) w))
      (adjunction f (relativelyRepresentable.targetYoneda hf))).symm

end morphismOfTopoiIn

variable [∀ P : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op P]

/-- For every presheaf and target object, the canonical comparison from right
Kan extension to evaluation at the representing object is an isomorphism. -/
instance representingFunctor_pushforward_obj (F : X.totalᵒᵖ ⥤ Type w)
    (y : Y.total) :
    IsIso (pushforwardComparison f (relativelyRepresentable.targetYoneda hf) F y) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
