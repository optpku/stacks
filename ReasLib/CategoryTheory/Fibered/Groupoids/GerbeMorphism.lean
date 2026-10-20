/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms of categories fibred in groupoids

The site-local gerbe-morphism property is owned by `CartesianBasedFunctor`. This leaf exposes
transparent groupoid-fibred views through the underlying universe-polymorphic cartesian functor,
without restating its defining conditions.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.Hom

variable {X Y Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- A morphism of categories fibred in groupoids is locally essentially surjective when its
underlying heterogeneous cartesian functor is. -/
@[stacks 06P2 "groupoid-fibred objectwise local-surjectivity criterion"]
abbrev LocallyEssentiallySurjective
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.LocallyEssentiallySurjective J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- A morphism of categories fibred in groupoids is homwise locally surjective when its
underlying heterogeneous cartesian functor is. -/
@[stacks 06P2 "groupoid-fibred Hom-presheaf criterion"]
abbrev Homwise.IsLocallySurjective
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.Homwise.IsLocallySurjective J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- A morphism of categories fibred in groupoids locally lifts fiber morphisms when its
underlying heterogeneous cartesian functor does. -/
@[stacks 06P2 "groupoid-fibred local-lifting criterion"]
abbrev LocallyLifts
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.LocallyLifts J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- A morphism of categories fibred in groupoids is a gerbe morphism when its underlying
heterogeneous cartesian functor is. -/
@[stacks 06P2 "gerbe morphism of groupoid-fibred categories"]
abbrev IsGerbeMorphism
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsGerbeMorphism J
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)

/-- The two defining local conditions of a gerbe morphism between groupoid-fibred categories. -/
@[stacks 06P2 "groupoid-fibred gerbe-morphism criterion"]
theorem isGerbeMorphism_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    IsGerbeMorphism J F ↔
      LocallyEssentiallySurjective J F ∧ Homwise.IsLocallySurjective J F := sorry

namespace IsGerbeMorphism

/-- A gerbe morphism between groupoid-fibred categories is locally essentially surjective. -/
@[stacks 06P2 "groupoid-fibred objectwise readout"]
theorem locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyEssentiallySurjective J F := sorry

/-- A gerbe morphism between groupoid-fibred categories is homwise locally surjective. -/
@[stacks 06P2 "groupoid-fibred Hom-presheaf readout"]
theorem homwiseLocallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    Homwise.IsLocallySurjective J F := sorry

/-- A gerbe morphism between groupoid-fibred categories locally lifts fiber morphisms. -/
@[stacks 06P2 "groupoid-fibred local-lifting readout"]
theorem locallyLifts
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyLifts J F := sorry

/-- Gerbe morphisms between groupoid-fibred categories are closed under composition. -/
@[stacks 06R3 "composition of groupoid-fibred gerbe morphisms"]
theorem comp
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : IsGerbeMorphism J F) (hG : IsGerbeMorphism J G) :
    IsGerbeMorphism J (F ≫ G) := sorry

/-- The gerbe-morphism property between groupoid-fibred categories is preserved when the
topology is enlarged. -/
theorem of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism K F := sorry

end IsGerbeMorphism

end FiberedCategoryOver.Groupoids.Hom

end CategoryTheory
