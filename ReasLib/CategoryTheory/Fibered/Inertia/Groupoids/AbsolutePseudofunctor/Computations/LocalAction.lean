/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor.Computations.Action

/-!
# Local-hom computations for groupoid-fibred inertia

This leaf exposes the strict and ordinary packaged local-hom actions at the
total-category level.  The direct typed `map₂` action remains the data owner.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict packaged local-hom action has the direct typed total transformation. -/
@[simp] theorem mapFunctor.map.toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ) =
      FiberedCategoryOver.Groupoids.toNatTrans
        (FiberedCategoryOver.Groupoids.Inertia.map₂ τ) := sorry

/-- A strict packaged local-hom action evaluates to the neutral inertia component. -/
@[simp] theorem mapFunctor.map.app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) A := sorry

/-- The underlying arrow of a strict packaged local-hom component is the original component. -/
@[simp] theorem mapFunctor.map.app.underlying
    {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app A) =
      (FiberedCategoryOver.Groupoids.toNatTrans τ).app A.obj := sorry

/-- Every strict packaged local-hom component is vertical over the identity on its base object. -/
theorem mapFunctor.map.app.isHomLift
    {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.inertia X).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app A) := sorry

/-- Strict packaged local-hom components are natural in total-category arrows. -/
@[reassoc] theorem mapFunctor.map.naturality
    {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor
      ((strictPseudofunctor C).mapFunctor X Y |>.obj F)).map f ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          ((strictPseudofunctor C).mapFunctor X Y |>.obj G)).map f := sorry

/-- Strict packaged local-hom `2`-cells agree when all total components agree. -/
theorem mapFunctor.map.ext
    {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ)).app A =
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map σ)).app A) :
    ((strictPseudofunctor C).mapFunctor X Y).map τ =
      ((strictPseudofunctor C).mapFunctor X Y).map σ := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary packaged local-hom action has the direct typed total transformation. -/
@[simp] theorem mapFunctor.map.toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ) =
      FiberedCategoryOver.Groupoids.toNatTrans
        (FiberedCategoryOver.Groupoids.Inertia.map₂ τ) := sorry

/-- An ordinary packaged local-hom action evaluates to the neutral inertia component. -/
@[simp] theorem mapFunctor.map.app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((pseudofunctor C).mapFunctor X Y |>.map τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) A := sorry

/-- The underlying arrow of an ordinary packaged local-hom component is the original component. -/
@[simp] theorem mapFunctor.map.app.underlying
    {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map τ)).app A) =
      (FiberedCategoryOver.Groupoids.toNatTrans τ).app A.obj := sorry

/-- Every ordinary packaged local-hom component is vertical over the identity on its base object. -/
theorem mapFunctor.map.app.isHomLift
    {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.inertia X).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ)).app A) := sorry

/-- Ordinary packaged local-hom components are natural in total-category arrows. -/
@[reassoc] theorem mapFunctor.map.naturality
    {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor
      ((pseudofunctor C).mapFunctor X Y |>.obj F)).map f ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map τ)).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ)).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          ((pseudofunctor C).mapFunctor X Y |>.obj G)).map f := sorry

/-- Ordinary packaged local-hom `2`-cells agree when all total components agree. -/
theorem mapFunctor.map.ext
    {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Groupoids.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ)).app A =
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map σ)).app A) :
    ((pseudofunctor C).mapFunctor X Y).map τ =
      ((pseudofunctor C).mapFunctor X Y).map σ := sorry

end pseudofunctor

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
