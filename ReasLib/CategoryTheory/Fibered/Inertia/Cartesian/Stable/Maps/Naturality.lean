module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans.Construction

/-!
# Naturality for stable-universe cartesian inertia maps

This leaf records `1`-cell and `2`-cell naturality for the forgetful map and identity section,
including the direct pseudofunctor forms used by strong-transformation clients.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- Bundled inertia maps commute with forgetting the automorphism. -/
@[simp, stacks 04Z4 "cartesian inertia map/forget naturality"]
theorem forget.naturality (F : X ⟶ Y) :
    FiberedCategoryOver.Inertia.map F ≫ forget Y = forget X ≫ F := sorry

/-- Bundled inertia maps carry the identity-automorphism section to the identity section. -/
@[simp, stacks 04Z4 "cartesian inertia map/identity-section naturality"]
theorem identitySection.naturality (F : X ⟶ Y) :
    identitySection X ≫ FiberedCategoryOver.Inertia.map F =
      F ≫ identitySection Y := sorry

/-- Forgetting the automorphism is `2`-natural for bundled fibred inertia. -/
@[stacks 04Z4 "cartesian inertia forgetful 2-naturality"]
theorem forget.naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    map₂ τ ▷ forget Y =
      eqToHom (forget.naturality F) ≫ forget X ◁ τ ≫
        eqToHom (forget.naturality G).symm := sorry

/-- The identity-automorphism section is `2`-natural for bundled fibred inertia. -/
@[stacks 04Z4 "cartesian inertia identity-section 2-naturality"]
theorem identitySection.naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    identitySection X ◁ map₂ τ =
      eqToHom (identitySection.naturality F) ≫ τ ▷ identitySection Y ≫
        eqToHom (identitySection.naturality G).symm := sorry

namespace pseudofunctor

/-- Naturality of the forgetful morphism on the ordinary inertia pseudofunctor. -/
@[simp, stacks 04Z4 "cartesian inertia pseudofunctor forgetful naturality"]
theorem forget.naturality (F : X ⟶ Y) :
    (FiberedCategoryOver.Inertia.pseudofunctor C).map F ≫ forget Y =
      forget X ≫
        (Pseudofunctor.id
          (FiberedCategoryOver.{u, v, max w vS, vS} C)).map F := sorry

/-- Naturality of the identity section on the ordinary inertia pseudofunctor. -/
@[simp, stacks 04Z4 "cartesian inertia pseudofunctor identity-section naturality"]
theorem identitySection.naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (FiberedCategoryOver.{u, v, max w vS, vS} C)).map F ≫ identitySection Y =
      identitySection X ≫
        (FiberedCategoryOver.Inertia.pseudofunctor C).map F := sorry

end pseudofunctor

end FiberedCategoryOver.Inertia

end CategoryTheory
