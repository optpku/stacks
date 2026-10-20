/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf.LocallySurjective

/-!
# Morphisms of stacks in groupoids

This file provides the canonical projections and direct lift between morphisms of stacks in
groupoids and morphisms of their underlying groupoid-fibred categories.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids J}

/-- The underlying morphism in the groupoid-fibred 2-category. -/
@[stacks 02ZK "underlying groupoid-fibred morphism of a stack morphism"]
abbrev toGroupoidsMor (F : X ⟶ Y) : X.toGroupoids ⟶ Y.toGroupoids :=
  F.hom

/-- Forget a `2`-isomorphism of groupoid-stack morphisms to the corresponding
`2`-isomorphism of groupoid-fibred morphisms. -/
@[stacks 02ZK "underlying groupoid-fibred morphism isomorphism"]
def toGroupoidsMorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toGroupoidsMor F ≅ toGroupoidsMor G :=
  Bicategory.InducedBicategory.Iso.toAmbient e

/-- The underlying morphism in the ambient bicategory of fibred categories. -/
@[stacks 02ZK "underlying fibred-category morphism of a stack morphism"]
abbrev toFiberedMor (F : X ⟶ Y) :
    X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver :=
  (FiberedCategoryOver.Groupoids.toFibered C).map (toGroupoidsMor F)

/-- The universe-polymorphic cartesian based functor underlying a morphism of stacks in
groupoids. This is the canonical view for local morphism properties. -/
@[stacks 02XP "cartesian-functor view of a groupoid-stack morphism"]
abbrev toCartesianBasedFunctor (F : X ⟶ Y) :
    CartesianBasedFunctor X.p Y.p :=
  FiberedCategoryOver.Groupoids.toCartesianBasedFunctor (toGroupoidsMor F)

/-- The underlying based functor. -/
@[stacks 02ZK "underlying based functor of a groupoid-stack morphism"]
abbrev toBasedFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.Groupoids.toBasedFunctor (toGroupoidsMor F)

/-- Forget a `2`-isomorphism of groupoid-stack morphisms directly to the corresponding
isomorphism of based functors. -/
@[stacks 02ZK "underlying based-functor isomorphism"]
noncomputable def toBasedFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  FiberedCategoryOver.Groupoids.toBasedFunctorIso (toGroupoidsMorIso e)

/-- The underlying functor on total categories. -/
@[stacks 02ZK "underlying total functor of a groupoid-stack morphism"]
abbrev toFunctor (F : X ⟶ Y) := (toBasedFunctor F).toFunctor

/-- The commutation `toFunctor F ⋙ Y.p = X.p`. -/
@[stacks 02ZK "projection commutation of a groupoid-stack morphism"]
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

/-- The induced functor on the fiber over `U`. -/
@[stacks 02ZK "fiber functor of a groupoid-stack morphism"]
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

/-- Lift a morphism of groupoid-fibred categories to a morphism of stacks in groupoids. -/
@[stacks 02ZK "lift of a groupoid-fibred stack morphism"]
abbrev lift (F : X.toGroupoids ⟶ Y.toGroupoids) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- A morphism of stacks in groupoids is an equivalence over the base if its underlying based
functor is. -/
@[stacks 02ZK "equivalence predicate for a groupoid-stack morphism"]
abbrev IsEquivalence (F : X ⟶ Y) : Prop := (toBasedFunctor F).IsEquivalence

/-- Every object of every target fiber is locally in the essential image. -/
@[stacks 02ZK "local essential-surjectivity predicate for groupoid-stack morphisms"]
abbrev LocallyEssentiallySurjective (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.LocallyEssentiallySurjective J
    (toCartesianBasedFunctor F)

/-- A stack morphism is homwise locally surjective when its underlying heterogeneous cartesian
functor is locally surjective on every minimally lifted canonical Hom-presheaf. -/
@[stacks 02ZK "homwise local-surjectivity predicate for groupoid-stack morphisms"]
abbrev Homwise.IsLocallySurjective (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.Homwise.IsLocallySurjective J
    (toCartesianBasedFunctor F)

/-- A stack morphism locally lifts fiber morphisms when its underlying heterogeneous cartesian
functor does. -/
@[stacks 02ZK "local lifting predicate for groupoid-stack morphisms"]
abbrev LocallyLifts (F : X ⟶ Y) : Prop :=
  Homwise.IsLocallySurjective F

end StackOver.Groupoids.Hom

end CategoryTheory
