/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Computations.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Whiskering

/-!
# Two-cell computations for typed groupoid-fibred inertia

This leaf records the projections, components, naturality, extensionality,
vertical functoriality, and whiskering formulas of the typed inertia action.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

namespace map₂

/-- The stable based-natural-transformation view of a typed inertia `2`-cell. -/
@[simp]
theorem toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans (map₂ τ) =
      BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) := sorry

/-- The based natural transformation view of a typed inertia `2`-cell. -/
@[simp]
theorem toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ) =
      (BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Groupoids.toBasedNatTrans τ)).toNatTrans := sorry

/-- Evaluating a typed inertia `2`-cell gives the neutral intertwined component. -/
@[simp]
theorem app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) A := sorry

/-- Each typed inertia `2`-cell component is a vertical hom-lift. -/
theorem app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app A) := sorry

/-- The underlying arrow of a typed inertia `2`-cell component is the original component. -/
@[simp]
theorem app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app A) =
      (FiberedCategoryOver.Groupoids.toNatTrans τ).app A.obj := sorry

/-- Typed inertia `2`-cell components are natural in inertia arrows. -/
@[reassoc]
theorem naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor (map F)).map f ≫
        (FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor (map G)).map f := sorry

/-- Two typed inertia 2-cells agree when all total-category components agree. -/
theorem ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Groupoids.toNatTrans (map₂ τ)).app A =
        (FiberedCategoryOver.Groupoids.toNatTrans (map₂ σ)).app A) :
    map₂ τ = map₂ σ := sorry

/-- Typed inertia is compatible with left whiskering. -/
theorem whiskerLeft
    {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (τ : G ⟶ H) :
    map₂ (F ◁ τ) =
      eqToHom (map.comp F G) ≫
        map F ◁ map₂ τ ≫
          eqToHom (map.comp F H).symm := sorry

/-- Typed inertia is compatible with right whiskering. -/
theorem whiskerRight
    {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F G : X ⟶ Y} (τ : F ⟶ G) (H : Y ⟶ Z) :
    map₂ (τ ▷ H) =
      eqToHom (map.comp F H) ≫
        map₂ τ ▷ map H ≫
          eqToHom (map.comp G H).symm := sorry

end map₂

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
