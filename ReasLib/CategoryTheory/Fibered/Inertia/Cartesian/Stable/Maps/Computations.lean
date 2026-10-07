module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Forget.Computations

/-!
# Computations for stable-universe cartesian inertia maps

This leaf exposes based, cartesian, and total projections together with object, arrow, and
section computations. Naturality is provided by the sibling `Naturality` leaf.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- The underlying based functor of the bundled inertia forgetful morphism is the canonical
forgetful based functor. -/
@[simp, stacks 042H "cartesian inertia forgetful based readout"]
theorem forget.toBasedFunctor
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.toBasedFunctor (forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry

/-- Forgetting cartesian preservation from the fixed-universe owner recovers canonical
cartesian inertia forgetting. -/
@[simp, stacks 042H "cartesian inertia forgetful cartesian readout"]
theorem forget.toCartesianBasedFunctor
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.toCartesianBasedFunctor (forget X) =
      BasedCategory.Inertia.cartesianForget X.toBasedCategory := sorry

/-- The total functor of the bundled inertia forgetful morphism is the neutral forgetful functor. -/
@[simp, stacks 042H "cartesian inertia forgetful total readout"]
theorem forget.toFunctor
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.toFunctor (forget X) =
      RelativeInertia.forget X.toBasedCategory.toBase.toFunctor := sorry

/-- Forgetting a bundled inertia object returns its underlying total-category object. -/
@[simp, stacks 042H "cartesian inertia forgetful object readout"]
theorem forget.obj
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toFunctor (forget X)).obj A = A.obj := sorry

/-- Forgetting a bundled inertia morphism returns its underlying total-category arrow. -/
@[simp, stacks 042H "cartesian inertia forgetful arrow readout"]
theorem forget.map
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C)
    {A B : (FiberedCategoryOver.inertia X).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (forget X)).map φ = RelativeInertia.hom φ := sorry

/-- The underlying based functor of the bundled identity section is the canonical based section. -/
@[simp, stacks 04Z3 "cartesian inertia identity-section based readout"]
theorem identitySection.toBasedFunctor
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.toBasedFunctor (identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry

/-- The total functor of the bundled identity section is the neutral identity section. -/
@[simp, stacks 04Z3 "cartesian inertia identity-section total readout"]
theorem identitySection.toFunctor
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.toFunctor (identitySection X) =
      RelativeInertia.identitySection X.toBasedCategory.toBase.toFunctor := sorry

/-- The bundled identity section preserves the underlying total-category object. -/
@[simp, stacks 04Z3 "cartesian inertia identity-section object readout"]
theorem identitySection.obj
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) (A : X.total) :
    ((FiberedCategoryOver.toFunctor (identitySection X)).obj A).obj = A := sorry

/-- The bundled identity section equips every total-category object with its identity
automorphism. -/
@[simp, stacks 04Z3 "cartesian inertia identity-section automorphism readout"]
theorem identitySection.aut
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) (A : X.total) :
    ((FiberedCategoryOver.toFunctor (identitySection X)).obj A).aut = 1 := sorry

/-- The arrow underlying the image of a morphism under the bundled identity section is the
original total-category arrow. -/
@[simp, stacks 04Z3 "cartesian inertia identity-section arrow readout"]
theorem identitySection.hom
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C)
    {A B : X.total} (f : A ⟶ B) :
    RelativeInertia.hom ((FiberedCategoryOver.toFunctor (identitySection X)).map f) = f := sorry

/-- The bundled identity section is a right inverse to forgetting the inertia automorphism. -/
@[simp, stacks 04Z3 "cartesian inertia section/forget compatibility"]
theorem identitySection.comp_forget
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    identitySection X ≫ forget X = 𝟙 X := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
