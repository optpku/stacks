module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction

/-!
# Naturality of groupoid-fibred inertia transformations

This leaf exposes naturality first for the direct typed action and then for its
packaged pseudofunctor facade.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

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

namespace pseudofunctor

/-- Groupoid-fibred inertia pseudofunctor maps commute with forgetting the selected
automorphism. -/
@[simp]
theorem forget.naturality (F : X ⟶ Y) :
    (Inertia.pseudofunctor C).map F ≫ forget Y = forget X ≫ F := sorry

/-- The identity pseudofunctor map followed by the neutral section agrees with first taking the
neutral section and then applying groupoid-fibred inertia. -/
@[simp]
theorem identitySection.naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)).map F ≫
          identitySection Y =
      identitySection X ≫ (Inertia.pseudofunctor C).map F := sorry

/-- Forgetting the selected automorphism is `2`-natural for groupoid-fibred inertia. -/
theorem forget.naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (Inertia.pseudofunctor C).map₂ τ ▷ forget Y =
      eqToHom (forget.naturality F) ≫ forget X ◁ τ ≫
        eqToHom (forget.naturality G).symm := sorry

/-- The identity-automorphism section is `2`-natural for groupoid-fibred inertia. -/
theorem identitySection.naturality₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    identitySection X ◁ (Inertia.pseudofunctor C).map₂ τ =
      eqToHom (identitySection.naturality F).symm ≫
        τ ▷ identitySection Y ≫
          eqToHom (identitySection.naturality G) := sorry

end pseudofunctor

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
