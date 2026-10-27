/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Computations.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Whiskering

/-!
# Two-cell computations for typed setoid-fibred inertia

This leaf records the projections, components, naturality, extensionality,
vertical functoriality, and whiskering formulas of the typed inertia action.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace map₂

/-- The stable based-natural-transformation view of a typed inertia `2`-cell. -/
@[simp]
theorem toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toBasedNatTrans (map₂ τ) =
      BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ) := by
  rfl

/-- The based natural transformation view of a typed inertia `2`-cell. -/
@[simp]
theorem toNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toNatTrans (map₂ τ) =
      (BasedCategory.Inertia.map₂
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ)).toNatTrans := by
  rfl

/-- Evaluating a typed inertia `2`-cell gives the neutral intertwined component. -/
@[simp]
theorem app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ) A := by
  rfl

/-- Each typed inertia `2`-cell component is a vertical hom-lift. -/
theorem app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app A) := by
  haveI := (FiberedCategoryOver.Setoids.toBasedNatTrans τ).isHomLift' A.obj
  refine IsHomLift.of_fac Y.inertia.p _ _ ?_ ?_ ?_
  · exact (FiberedCategoryOver.Setoids.toBasedFunctor F).w_obj A.obj
  · exact (FiberedCategoryOver.Setoids.toBasedFunctor G).w_obj A.obj
  · exact IsHomLift.fac Y.p (𝟙 (X.p.obj A.obj))
      ((FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj)

/-- The underlying arrow of a typed inertia `2`-cell component is the original component. -/
@[simp]
theorem app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj := by
  rfl

/-- Typed inertia `2`-cell components are natural in inertia arrows. -/
@[reassoc]
theorem naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : X.inertia.total} (f : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor (map F)).map f ≫
        (FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app B =
      (FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app A ≫
        (FiberedCategoryOver.Setoids.toFunctor (map G)).map f := by
  apply InducedCategory.hom_ext
  apply Subtype.ext
  exact (FiberedCategoryOver.Setoids.toNatTrans τ).naturality (RelativeInertia.hom f)

/-- Two typed inertia 2-cells agree when all total-category components agree. -/
theorem ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : X.inertia.total,
      (FiberedCategoryOver.Setoids.toNatTrans (map₂ τ)).app A =
        (FiberedCategoryOver.Setoids.toNatTrans (map₂ σ)).app A) :
    map₂ τ = map₂ σ := by
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  exact NatTrans.ext (funext h)

/-- Typed inertia is compatible with left whiskering. -/
theorem whiskerLeft
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (τ : G ⟶ H) :
    map₂ (F ◁ τ) =
      eqToHom (map.comp F G) ≫
        map F ◁ map₂ τ ≫
          eqToHom (map.comp F H).symm := by
  change map₂ (F ◁ τ) = 𝟙 _ ≫ map F ◁ map₂ τ ≫ 𝟙 _
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext A
  apply InducedCategory.hom_ext
  apply Subtype.ext
  change (FiberedCategoryOver.Setoids.toNatTrans τ).app
      ((FiberedCategoryOver.Setoids.toFunctor F).obj A.obj) =
    𝟙 _ ≫ (FiberedCategoryOver.Setoids.toNatTrans τ).app
      ((FiberedCategoryOver.Setoids.toFunctor F).obj A.obj) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- Typed inertia is compatible with right whiskering. -/
theorem whiskerRight
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F G : X ⟶ Y} (τ : F ⟶ G) (H : Y ⟶ Z) :
    map₂ (τ ▷ H) =
      eqToHom (map.comp F H) ≫
        map₂ τ ▷ map H ≫
          eqToHom (map.comp G H).symm := by
  change map₂ (τ ▷ H) = 𝟙 _ ≫ map₂ τ ▷ map H ≫ 𝟙 _
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext A
  apply InducedCategory.hom_ext
  apply Subtype.ext
  change (FiberedCategoryOver.Setoids.toFunctor H).map
      ((FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj) =
    𝟙 _ ≫ (FiberedCategoryOver.Setoids.toFunctor H).map
      ((FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

end map₂

end FiberedCategoryOver.Setoids.Inertia

end CategoryTheory
