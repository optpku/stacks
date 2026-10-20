/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homwise local surjectivity for morphisms of fibred categories

This file exposes the fixed-universe view of the universe-polymorphic
`CartesianBasedFunctor.Homwise.IsLocallySurjective` owner. Its pointwise readout uses the
unlifted canonical Hom-presheaf map available when both total categories have the same morphism
universe.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory.FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.{u, v, uS, vS} C}

/-- A morphism of fibred categories is homwise locally surjective when every canonical
Hom-presheaf map is locally surjective on the corresponding slice site. -/
abbrev Homwise.IsLocallySurjective
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.Homwise.IsLocallySurjective J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The fibred-category homwise condition is pointwise local surjectivity of its canonical
Hom-presheaf maps. -/
theorem Homwise.isLocallySurjective_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    Homwise.IsLocallySurjective J F ↔
      ∀ {U : C} (x y : X.p.Fiber U),
        Presheaf.IsLocallySurjective (J.over U) (presheafHomMap F x y) := sorry

/-- Every canonical Hom-presheaf map of a homwise locally surjective morphism is locally
surjective. -/
theorem Homwise.IsLocallySurjective.presheafHomMap
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : Homwise.IsLocallySurjective J F)
    {U : C} (x y : X.p.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (presheafHomMap F x y) := sorry

/-- Homwise locally surjective morphisms of fibred categories are closed under composition. -/
theorem Homwise.IsLocallySurjective.comp
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : Homwise.IsLocallySurjective J F)
    (hG : Homwise.IsLocallySurjective J G) :
    Homwise.IsLocallySurjective J (F ≫ G) := sorry

/-- Homwise local surjectivity is preserved when the topology is enlarged. -/
theorem Homwise.IsLocallySurjective.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K) {F : X ⟶ Y}
    (hF : Homwise.IsLocallySurjective J F) :
    Homwise.IsLocallySurjective K F := sorry

/-- An equivalence over the base is locally surjective on every canonical Hom-presheaf. -/
theorem Homwise.IsLocallySurjective.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    Homwise.IsLocallySurjective J F := sorry

/-- Transport homwise local surjectivity along an isomorphism of parallel morphisms of fibred
categories. -/
theorem Homwise.IsLocallySurjective.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : Homwise.IsLocallySurjective J F) :
    Homwise.IsLocallySurjective J G := sorry

/-- Parallel isomorphic morphisms of fibred categories are homwise locally surjective
simultaneously. -/
theorem Homwise.isLocallySurjective_iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    Homwise.IsLocallySurjective J F ↔ Homwise.IsLocallySurjective J G := sorry

end CategoryTheory.FiberedCategoryOver.Hom
