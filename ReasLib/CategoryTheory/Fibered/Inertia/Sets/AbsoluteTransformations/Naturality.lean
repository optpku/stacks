module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Construction

/-!
# Naturality of set-fibred inertia transformations

This leaf exposes naturality first for the direct typed action and then for its
packaged pseudofunctor facade.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}

namespace map

/-- A direct typed inertia map commutes with forgetting the selected automorphism. -/
@[simp]
theorem comp_forget (F : X ⟶ Y) :
    map F ≫ forget Y = forget X ≫ F := sorry

end map

namespace identitySection

/-- The identity section is natural for the direct typed inertia action. -/
@[simp]
theorem comp_map (F : X ⟶ Y) :
    identitySection X ≫ map F = F ≫ identitySection Y := sorry

end identitySection

namespace map₂

/-- Forgetting the selected automorphism is `2`-natural for the direct typed action. -/
theorem whiskerRight.forget {F G : X ⟶ Y} (τ : F ⟶ G) :
    map₂ τ ▷ forget Y =
      eqToHom (map.comp_forget F) ≫ forget X ◁ τ ≫
        eqToHom (map.comp_forget G).symm := sorry

/-- The identity-automorphism section is `2`-natural for the direct typed action. -/
theorem identitySection.naturality {F G : X ⟶ Y} (τ : F ⟶ G) :
    identitySection X ◁ map₂ τ =
      eqToHom (identitySection.comp_map F) ≫
        τ ▷ identitySection Y ≫
          eqToHom (identitySection.comp_map G).symm := sorry

end map₂

namespace pseudofunctor.forget

/-- Set-fibred inertia maps commute with forgetting the selected automorphism. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (pseudofunctor C).map F ≫ forget Y = forget X ≫ F := sorry

/-- Inertia forgetting is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (pseudofunctor C).map₂ τ ▷ forget Y =
      eqToHom (naturality F) ≫ forget X ◁ τ ≫
        eqToHom (naturality G).symm := sorry

end pseudofunctor.forget

namespace pseudofunctor.identitySection

/-- The set-fibred identity section is natural in `1`-morphisms. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)).map F ≫
          identitySection Y =
      identitySection X ≫ (pseudofunctor C).map F := sorry

/-- The set-fibred identity section is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    identitySection X ◁ (pseudofunctor C).map₂ τ =
      eqToHom (naturality F).symm ≫ τ ▷ identitySection Y ≫
        eqToHom (naturality G) := sorry

end pseudofunctor.identitySection

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
