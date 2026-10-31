/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Biequivalence
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Grothendieck

/-!
# Equivalence properties of fibrewise components

This file isolates the equivalence, essential-surjectivity, and Hom-space consequences of the
fibrewise-components constructions from their underlying data and computation API.
-/

@[expose] public section

universe u v vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

/-- Taking fibrewise components gives an equivalence from the homotopy category of categories
fibred in setoids to set-valued presheaves. The source total-category Hom universe contains
the base Hom universe, as required by the discrete Grothendieck construction. -/
@[stacks 04SC "presheaf equivalence from fibrewise components"]
instance componentsPresheaf.isEquivalence :
    (componentsPresheaf.{u, v, max v vS} C).IsEquivalence := sorry

/-- The fibrewise-component functor is an equivalence after homotopy `1`-truncation of its
bicategorical source. -/
@[stacks 04SC "equivalence after fibrewise components"]
instance components.isEquivalence :
    (components.{u, v, max v vS} C).IsEquivalence := by
  have h : components.{u, v, max v vS} C =
      componentsPresheaf.{u, v, max v vS} C ⋙ FiberedCategoryOver.Sets.ofPresheaf C := by
    refine Functor.hext (F := components.{u, v, max v vS} C)
      (G := componentsPresheaf.{u, v, max v vS} C ⋙ FiberedCategoryOver.Sets.ofPresheaf C)
      (fun _ ↦ rfl) ?_
    intro X Y f
    refine Quotient.inductionOn f ?_
    intro F
    rfl
  rw [h]
  infer_instance

/-- If two `1`-morphisms have the same image after taking fibrewise components, there exists a
unique `2`-isomorphism between them. -/
@[stacks 04SC "(2)"]
theorem components.uniqueIso_of_map_eq
    {X Y : FiberedCategoryOver.Setoids C} {F G : X ⟶ Y}
    (h : (components C).map
          (Bicategory.HomotopyCategory.mkHom F) =
        (components C).map
          (Bicategory.HomotopyCategory.mkHom G)) :
    Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := sorry

/-- Every morphism between associated categories fibred in sets is induced by a `1`-morphism of
the original categories fibred in setoids. -/
@[stacks 04SC "(3)"]
theorem components.map_surjective (X Y : FiberedCategoryOver.Setoids C) :
    Function.Surjective
      (fun F : X ⟶ Y ↦
        (components C).map
          (Bicategory.HomotopyCategory.mkHom F)) := sorry

variable (C) in
/-- Every category fibred in sets lies in the essential image of the fibrewise-component
functor. -/
@[stacks 04SC "(4)"]
theorem components.essSurj :
    (components.{u, v, max v vS} C).EssSurj := by
  infer_instance

/-- The fibrewise-components pseudofunctor induces an equivalence on every Hom category.

This is the bicategorical fully-faithful part of `components.isEquivalence`: surjectivity on
represented morphisms supplies essential surjectivity of each Hom functor, while uniqueness of
the induced `2`-isomorphism supplies its fully faithful part. -/
@[stacks 04SC "fibrewise components are locally an equivalence"]
theorem components.pseudofunctor.isLocallyEquivalence :
    (components.pseudofunctor C).IsLocallyEquivalence := by
  refine ⟨fun X Y ↦ ?_⟩
  let P := (components.pseudofunctor C).mapFunctor X Y
  haveI : P.Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
  haveI : P.Full := ⟨by
    intro F G η
    have h : (components C).map (Bicategory.HomotopyCategory.mkHom F) =
        (components C).map (Bicategory.HomotopyCategory.mkHom G) :=
      Discrete.eq_of_hom η
    obtain ⟨e⟩ := (components.uniqueIso_of_map_eq h).1
    exact ⟨e.hom, Subsingleton.elim _ _⟩⟩
  haveI : P.EssSurj := ⟨by
    intro f
    obtain ⟨F, hF⟩ := components.map_surjective X Y f.as
    exact ⟨F, ⟨Discrete.eqToIso hF⟩⟩⟩
  exact { }

/-- Every category fibred in sets lies in the bicategorical essential image of the
fibrewise-components pseudofunctor. -/
@[stacks 04SC "bicategorical essential surjectivity of fibrewise components"]
theorem components.pseudofunctor.essSurj :
    (components.pseudofunctor.{u, v, max v vS} C).EssSurj := by
  constructor
  intro Y
  obtain ⟨X, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage (F := components.{u, v, max v vS} C) Y.as
  refine ⟨X.as, ⟨{
    hom := e.hom.toLoc
    inv := e.inv.toLoc
    unit := Discrete.eqToIso e.hom_inv_id.symm
    counit := Discrete.eqToIso e.inv_hom_id
    left_triangle := Subsingleton.elim _ _ }⟩⟩

/-- Taking fibrewise components is a biequivalence from categories fibred in setoids to the
locally discrete bicategory of categories fibred in sets. -/
@[stacks 04SC "fibrewise-components biequivalence"]
instance components.pseudofunctor.isBiequivalence :
    (components.pseudofunctor.{u, v, max v vS} C).IsBiequivalence :=
  { components.pseudofunctor.isLocallyEquivalence,
    components.pseudofunctor.essSurj with }

/-- Morphisms of categories fibred in setoids modulo `2`-isomorphism are canonically identified
with morphisms of their fibrewise-component presheaves. -/
@[stacks 04SC "(5)"]
theorem componentsPresheaf.map_bijective (X Y : FiberedCategoryOver.Setoids C) :
    Function.Bijective
      ((componentsPresheaf C).map :
        (Bicategory.HomotopyCategory.mk X ⟶
          Bicategory.HomotopyCategory.mk Y) →
      (Functor.fiberIsoClassPresheaf X.p ⟶
          Functor.fiberIsoClassPresheaf Y.p)) := by
  constructor
  · intro f g h
    obtain ⟨F, rfl⟩ := Quotient.exists_rep f
    obtain ⟨G, rfl⟩ := Quotient.exists_rep g
    have hFG : (components C).map (Bicategory.HomotopyCategory.mkHom F) =
        (components C).map (Bicategory.HomotopyCategory.mkHom G) :=
      congrArg (FiberedCategoryOver.Sets.ofPresheaf C).map h
    obtain ⟨e⟩ := (components.uniqueIso_of_map_eq hFG).1
    exact Quotient.sound (Zigzag.of_hom e.hom)
  · intro f
    obtain ⟨F, hF⟩ :=
      components.map_surjective X Y ((FiberedCategoryOver.Sets.ofPresheaf C).map f)
    refine ⟨Bicategory.HomotopyCategory.mkHom F, ?_⟩
    apply (FiberedCategoryOver.Sets.ofPresheaf C).map_injective
    exact hF

end FiberedCategoryOver.Setoids

end CategoryTheory
