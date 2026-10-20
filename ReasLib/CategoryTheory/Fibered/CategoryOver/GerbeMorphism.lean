/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms of fibred categories

The universe-polymorphic owner is `CartesianBasedFunctor.IsGerbeMorphism`. This file exposes its
fixed-universe view for the bicategorical hom-category of fibred categories, together with
readouts in the established unlifted Hom-presheaf language.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom

variable {X Y Z : FiberedCategoryOver.{u, v, w, vS} C}

/-- A morphism of fibred categories is a gerbe morphism when it is locally essentially
surjective on objects and locally surjective on every canonical Hom-presheaf. This is the
fixed-universe specialization of `CartesianBasedFunctor.IsGerbeMorphism`. -/
@[stacks 06P2 "gerbe morphism of fibred categories"]
abbrev IsGerbeMorphism (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsGerbeMorphism J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The two defining local conditions of a gerbe morphism. -/
@[stacks 06P2 "fixed-universe gerbe-morphism criterion"]
theorem isGerbeMorphism_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    IsGerbeMorphism J F ↔
      LocallyEssentiallySurjective J F ∧
        Homwise.IsLocallySurjective J F := sorry

/-- A gerbe morphism is locally essentially surjective on fibre objects. -/
@[stacks 06P2 "fixed-universe objectwise readout"]
theorem IsGerbeMorphism.locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyEssentiallySurjective J F := sorry

/-- A gerbe morphism locally lifts fibre morphisms. -/
@[stacks 06P2 "fixed-universe local-lifting readout"]
theorem IsGerbeMorphism.locallyLifts
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyLifts J F := sorry

/-- A gerbe morphism is locally surjective on every canonical Hom-presheaf. -/
@[stacks 06P2 "fixed-universe Hom-presheaf readout"]
theorem IsGerbeMorphism.homwiseLocallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    Homwise.IsLocallySurjective J F := sorry

/-- The identity morphism is a gerbe morphism. -/
@[stacks 06R3 "identity gerbe morphism"]
theorem IsGerbeMorphism.id (J : GrothendieckTopology C) :
    IsGerbeMorphism J (𝟙 X) := sorry

/-- Gerbe morphisms of fibred categories are closed under composition. -/
@[stacks 06R3]
theorem IsGerbeMorphism.comp
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : IsGerbeMorphism J F) (hG : IsGerbeMorphism J G) :
    IsGerbeMorphism J (F ≫ G) := sorry

/-- The gerbe-morphism property of fibred categories is preserved when the topology is
enlarged. -/
theorem IsGerbeMorphism.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism K F := sorry

/-- An equivalence over the base is a gerbe morphism. -/
theorem IsGerbeMorphism.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    IsGerbeMorphism J F := sorry

/-- Transport the gerbe-morphism property along an isomorphism of parallel morphisms. -/
theorem IsGerbeMorphism.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism J G := sorry

/-- Isomorphic parallel morphisms are gerbe morphisms simultaneously. -/
theorem isGerbeMorphism_iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    IsGerbeMorphism J F ↔ IsGerbeMorphism J G := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
