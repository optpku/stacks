module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Basic.Action

/-!
# Strict coherence computations for stack inertia

Computations for the object, local action, identity comparison, and composition comparison of the
strict stack inertia pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Inertia.strictPseudofunctor

variable {X Y : StackOver.{u, v, w, vS} J}

/-- The strict stack inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp]
theorem obj (X : StackOver.{u, v, w, vS} J) :
    (StackOver.Inertia.strictPseudofunctor J).obj X = StackOver.inertia X := sorry

/-- Its `1`-cell field is the public stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Inertia.strictPseudofunctor J).map F = StackOver.inertia.map F := sorry

/-- Its `2`-cell field is the public stack inertia `2`-cell action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Inertia.strictPseudofunctor J).map₂ eta = StackOver.inertia.map₂ eta := sorry

/-- Its local action is the public stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.{u, v, w, vS} J) :
    (StackOver.Inertia.strictPseudofunctor J).mapFunctor X Y =
      StackOver.inertia.mapFunctor X Y := sorry

/-- The forward strict identity comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.{u, v, w, vS} J) :
    ((StackOver.Inertia.strictPseudofunctor J).mapId X).hom.hom =
      ((FiberedCategoryOver.Inertia.strictPseudofunctor C).mapId
        X.toFiberedCategoryOver).hom := sorry

/-- The inverse strict identity comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.{u, v, w, vS} J) :
    ((StackOver.Inertia.strictPseudofunctor J).mapId X).inv.hom =
      ((FiberedCategoryOver.Inertia.strictPseudofunctor C).mapId
        X.toFiberedCategoryOver).inv := sorry

/-- The forward strict composition comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Inertia.strictPseudofunctor J).mapComp F G).hom.hom =
      ((FiberedCategoryOver.Inertia.strictPseudofunctor C).mapComp
        (Hom.toMor F) (Hom.toMor G)).hom := sorry

/-- The inverse strict composition comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Inertia.strictPseudofunctor J).mapComp F G).inv.hom =
      ((FiberedCategoryOver.Inertia.strictPseudofunctor C).mapComp
        (Hom.toMor F) (Hom.toMor G)).inv := sorry

end StackOver.Inertia.strictPseudofunctor

end CategoryTheory
