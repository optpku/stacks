module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Basic.Action

/-!
# Ordinary coherence computations for stack inertia

Computations for the object, local action, identity comparison, and composition comparison of the
ordinary stack inertia pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Inertia.pseudofunctor

variable {X Y : StackOver.{u, v, w, vS} J}

/-- The ordinary stack inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp]
theorem obj (X : StackOver.{u, v, w, vS} J) :
    (StackOver.Inertia.pseudofunctor J).obj X = StackOver.inertia X := sorry

/-- Its `1`-cell action is the public stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Inertia.pseudofunctor J).map F = StackOver.inertia.map F := sorry

/-- Its `2`-cell action is the public stack inertia `2`-cell action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Inertia.pseudofunctor J).map₂ eta = StackOver.inertia.map₂ eta := sorry

/-- Its local action is the public stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.{u, v, w, vS} J) :
    (StackOver.Inertia.pseudofunctor J).mapFunctor X Y =
      StackOver.inertia.mapFunctor X Y := sorry

/-- The forward ordinary identity comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.{u, v, w, vS} J) :
    ((StackOver.Inertia.pseudofunctor J).mapId X).hom.hom =
      ((FiberedCategoryOver.Inertia.pseudofunctor C).mapId
        X.toFiberedCategoryOver).hom := sorry

/-- The inverse ordinary identity comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.{u, v, w, vS} J) :
    ((StackOver.Inertia.pseudofunctor J).mapId X).inv.hom =
      ((FiberedCategoryOver.Inertia.pseudofunctor C).mapId
        X.toFiberedCategoryOver).inv := sorry

/-- The forward ordinary composition comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Inertia.pseudofunctor J).mapComp F G).hom.hom =
      ((FiberedCategoryOver.Inertia.pseudofunctor C).mapComp
        (Hom.toMor F) (Hom.toMor G)).hom := sorry

/-- The inverse ordinary composition comparison forgets to the neutral fibred comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Inertia.pseudofunctor J).mapComp F G).inv.hom =
      ((FiberedCategoryOver.Inertia.pseudofunctor C).mapComp
        (Hom.toMor F) (Hom.toMor G)).inv := sorry

end StackOver.Inertia.pseudofunctor

end CategoryTheory
