/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Computations.TwoCell

/-!
# Packaged two-cell computations for setoid-fibred inertia

This leaf exposes total-category components and naturality for the strict and ordinary packaged
pseudofunctors, while retaining the direct typed action as the data owner.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The total natural transformation underlying a strict packaged `2`-cell is the direct typed
inertia transformation. -/
@[simp] theorem map₂.toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toNatTrans ((strictPseudofunctor C).map₂ τ) =
      FiberedCategoryOver.Setoids.toNatTrans
        (FiberedCategoryOver.Setoids.Inertia.map₂ τ) := sorry

/-- A strict packaged `2`-cell evaluates to the neutral inertia component. -/
@[simp] theorem map₂.app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
      ((strictPseudofunctor C).map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ) A := sorry

/-- The underlying arrow of a strict packaged component is the original total component. -/
@[simp] theorem map₂.app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((strictPseudofunctor C).map₂ τ)).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj := sorry

/-- Every strict packaged component is vertical over the identity on its base object. -/
theorem map₂.app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Setoids.inertia X).p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans
        ((strictPseudofunctor C).map₂ τ)).app A) := sorry

/-- Strict packaged components are natural in total-category arrows. -/
@[reassoc] theorem map₂.naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor
      ((strictPseudofunctor C).map F)).map f ≫
        (FiberedCategoryOver.Setoids.toNatTrans
          ((strictPseudofunctor C).map₂ τ)).app B =
      (FiberedCategoryOver.Setoids.toNatTrans
        ((strictPseudofunctor C).map₂ τ)).app A ≫
        (FiberedCategoryOver.Setoids.toFunctor
          ((strictPseudofunctor C).map G)).map f := sorry

/-- Two strict packaged `2`-cells agree when all total-category components agree. -/
theorem map₂.ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Setoids.toNatTrans
        ((strictPseudofunctor C).map₂ τ)).app A =
        (FiberedCategoryOver.Setoids.toNatTrans
          ((strictPseudofunctor C).map₂ σ)).app A) :
    (strictPseudofunctor C).map₂ τ = (strictPseudofunctor C).map₂ σ := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The total natural transformation underlying an ordinary packaged `2`-cell is the direct
typed inertia transformation. -/
@[simp] theorem map₂.toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toNatTrans ((pseudofunctor C).map₂ τ) =
      FiberedCategoryOver.Setoids.toNatTrans
        (FiberedCategoryOver.Setoids.Inertia.map₂ τ) := sorry

/-- An ordinary packaged `2`-cell evaluates to the neutral inertia component. -/
@[simp] theorem map₂.app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
      ((pseudofunctor C).map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ) A := sorry

/-- The underlying arrow of an ordinary packaged component is the original total component. -/
@[simp] theorem map₂.app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((pseudofunctor C).map₂ τ)).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj := sorry

/-- Every ordinary packaged component is vertical over the identity on its base object. -/
theorem map₂.app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Setoids.inertia X).p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans
        ((pseudofunctor C).map₂ τ)).app A) := sorry

/-- Ordinary packaged components are natural in total-category arrows. -/
@[reassoc] theorem map₂.naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor ((pseudofunctor C).map F)).map f ≫
        (FiberedCategoryOver.Setoids.toNatTrans
          ((pseudofunctor C).map₂ τ)).app B =
      (FiberedCategoryOver.Setoids.toNatTrans
        ((pseudofunctor C).map₂ τ)).app A ≫
        (FiberedCategoryOver.Setoids.toFunctor ((pseudofunctor C).map G)).map f := sorry

/-- Two ordinary packaged `2`-cells agree when all total-category components agree. -/
theorem map₂.ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Setoids.toNatTrans
        ((pseudofunctor C).map₂ τ)).app A =
        (FiberedCategoryOver.Setoids.toNatTrans
          ((pseudofunctor C).map₂ σ)).app A) :
    (pseudofunctor C).map₂ τ = (pseudofunctor C).map₂ σ := sorry

end pseudofunctor

end FiberedCategoryOver.Setoids.Inertia

end CategoryTheory
