/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Basic

/-!
# Indexed comparison of cleavages

The identity cartesian based functor gives the canonical indexed comparison
between the pseudofunctors associated to two cleavages of one projection.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Functor.Cleavage

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S] {p : S ⥤ C}

/-- The coherent identity-on-fibers comparison between the pseudofunctors defined by two
cleavages on the same projection. -/
noncomputable def Indexed.comparison (χ₁ χ₂ : p.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      χ₁.toPseudofunctor χ₂.toPseudofunctor :=
  CartesianBasedFunctor.Indexed.explicit.functor (CartesianBasedFunctor.id p) χ₁ χ₂

/-- Every component of a change-of-cleavage indexed functor is the identity fiber functor. -/
@[simp]
theorem Indexed.comparison.app
    (χ₁ χ₂ : p.Cleavage) (U : C) :
    (Indexed.comparison χ₁ χ₂).app U = 𝟭 (p.Fiber U) := sorry

/-- Forward naturality for changing cleavage is the inverse comparison between the two selected
reindexing functors. -/
@[simp]
theorem Indexed.comparison.naturality.hom.app
    (χ₁ χ₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    ((Indexed.comparison χ₁ χ₂).naturality f).hom.app x =
      (Reindex.uniqueIsoApp χ₁ χ₂ f x).hom := sorry

/-- Inverse naturality for changing cleavage is the forward comparison between the two selected
reindexing functors. -/
@[simp]
theorem Indexed.comparison.naturality.inv.app
    (χ₁ χ₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    ((Indexed.comparison χ₁ χ₂).naturality f).inv.app x =
      (Reindex.uniqueIsoApp χ₁ χ₂ f x).inv := sorry

/-- Changing cleavage preserves restricted morphisms by conjugation with the canonical
reindexing comparisons. -/
@[simp]
theorem Indexed.comparison.mapHom
    (χ₁ χ₂ : p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p.Fiber U₁} {y : p.Fiber U₂}
    (φ :
      (χ₁.toPseudofunctor.map f₁.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f₂.op.toLoc).toFunctor.obj y) :
    (Indexed.comparison χ₁ χ₂).mapHom f₁ f₂ φ =
      (Reindex.uniqueIsoApp χ₁ χ₂ f₁ x).inv ≫
        φ ≫ (Reindex.uniqueIsoApp χ₁ χ₂ f₂ y).hom := sorry

/-- Total-category readout of restricted-morphism transport through a change of cleavage. -/
theorem Indexed.comparison.mapHom.toTotal
    (χ₁ χ₂ : p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p.Fiber U₁} {y : p.Fiber U₂}
    (φ :
      (χ₁.toPseudofunctor.map f₁.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f₂.op.toLoc).toFunctor.obj y) :
    ((Indexed.comparison χ₁ χ₂).mapHom f₁ f₂ φ).1 =
      (Reindex.uniqueIsoApp χ₁ χ₂ f₁ x).inv.1 ≫
        φ.1 ≫ (Reindex.uniqueIsoApp χ₁ χ₂ f₂ y).hom.1 := sorry

/-- The change-of-cleavage indexed functor from a cleavage to itself is the identity indexed
functor. -/
@[simp]
theorem Indexed.comparison.self
    (χ : p.Cleavage) :
    Indexed.comparison χ χ =
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.id
        χ.toPseudofunctor := sorry

/-- Successive changes of cleavage compose to the canonical direct change of cleavage. -/
@[simp]
theorem Indexed.comparison.trans
    (χ₁ χ₂ χ₃ : p.Cleavage) :
    (Indexed.comparison χ₁ χ₂).comp
        (Indexed.comparison χ₂ χ₃) =
      Indexed.comparison χ₁ χ₃ := sorry

/-- A change-of-cleavage indexed functor is an equivalence on every fiber. -/
instance Indexed.comparison.fiberwiseEquivalence
    (χ₁ χ₂ : p.Cleavage) :
    (Indexed.comparison χ₁ χ₂).FiberwiseEquivalence := sorry

end Functor.Cleavage

end CategoryTheory
