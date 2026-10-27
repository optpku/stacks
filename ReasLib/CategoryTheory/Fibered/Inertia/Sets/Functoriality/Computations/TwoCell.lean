/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Computations.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Whiskering

/-!
# Two-cell computations for typed set-fibred inertia

This leaf records the projections, components, naturality, extensionality,
vertical functoriality, and whiskering formulas of the typed inertia action.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

namespace map₂

/-- The based natural-transformation view of a typed set-fibred inertia `2`-cell. -/
@[simp]
theorem toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Sets.toBasedNatTrans (map₂ τ) =
      BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Sets.toBasedNatTrans τ) := rfl

/-- The total natural-transformation view of a typed set-fibred inertia `2`-cell. -/
@[simp]
theorem toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Sets.toNatTrans (map₂ τ) =
      (BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Sets.toBasedNatTrans τ)).toNatTrans := rfl

/-- Evaluating a typed set-fibred inertia `2`-cell gives the neutral intertwined component. -/
@[simp]
theorem app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Sets.toBasedNatTrans τ) A := rfl

/-- Each typed set-fibred inertia `2`-cell component is a vertical hom-lift. -/
theorem app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app A) := by
  exact (FiberedCategoryOver.Sets.toBasedNatTrans (map₂ τ)).isHomLift' A

/-- The underlying arrow of a typed set-fibred inertia `2`-cell component is the original
natural-transformation component. -/
@[simp]
theorem app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app A) =
      (FiberedCategoryOver.Sets.toNatTrans τ).app A.obj := rfl

/-- Typed set-fibred inertia `2`-cell components are natural in inertia arrows. -/
@[reassoc]
theorem naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Sets.toFunctor (map F)).map f ≫
        (FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app B =
      (FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app A ≫
        (FiberedCategoryOver.Sets.toFunctor (map G)).map f := by
  exact (FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).naturality f

/-- Two typed set-fibred inertia `2`-cells agree when all total-category components agree. -/
theorem ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Sets.toNatTrans (map₂ τ)).app A =
        (FiberedCategoryOver.Sets.toNatTrans (map₂ σ)).app A) :
    map₂ τ = map₂ σ := by
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  exact NatTrans.ext (funext h)

/-- Typed set-fibred inertia is compatible with left whiskering. -/
theorem whiskerLeft
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (τ : G ⟶ H) :
    map₂ (F ◁ τ) =
      eqToHom (map.comp F G) ≫
        map F ◁ map₂ τ ≫
          eqToHom (map.comp F H).symm := by
  change map₂ (F ◁ τ) = 𝟙 _ ≫ map F ◁ map₂ τ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- Typed set-fibred inertia is compatible with right whiskering. -/
theorem whiskerRight
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F G : X ⟶ Y} (τ : F ⟶ G) (H : Y ⟶ Z) :
    map₂ (τ ▷ H) =
      eqToHom (map.comp F H) ≫
        map₂ τ ▷ map H ≫
          eqToHom (map.comp G H).symm := by
  change map₂ (τ ▷ H) = 𝟙 _ ≫ map₂ τ ▷ map H ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

end map₂

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
