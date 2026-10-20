module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Whiskering

/-!
# Computations for the cartesian inertia `2`-cell action

This leaf exposes based and total projections, component formulas, naturality, extensionality,
and whiskering for the bundled cartesian action.
-/

@[expose] public section

universe u v uS vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace map₂

/-- The semantic based-natural-transformation projection of a cartesian inertia `2`-cell is the
neutral inertia action. -/
@[simp, stacks 04Z4 "cartesian inertia two-cell based readout"]
theorem toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans (map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ) := sorry

/-- Evaluation of a cartesian inertia `2`-morphism is the explicit neutral inertia component. -/
@[simp, stacks 04Z4 "cartesian inertia two-cell component readout"]
theorem app {F G : X ⟶ Y} (τ : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans (map₂ τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.toBasedNatTrans τ) A := sorry

/-- Every component of a cartesian inertia `2`-morphism is vertical over the unchanged base
object. -/
@[stacks 04Z4 "cartesian inertia two-cell verticality"]
theorem app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans (map₂ τ)).app A) := sorry

/-- The underlying arrow of a cartesian inertia `2`-morphism is the original component. -/
@[simp, stacks 04Z4 "cartesian inertia two-cell underlying component"]
theorem app.underlying {F G : X ⟶ Y} (τ : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom ((FiberedCategoryOver.toNatTrans (map₂ τ)).app A) =
      (FiberedCategoryOver.toNatTrans τ).app A.obj := sorry

/-- Naturality of the cartesian inertia `2`-morphism on total categories. -/
@[reassoc, stacks 04Z4 "cartesian inertia two-cell naturality"]
theorem naturality {F G : X ⟶ Y} (τ : F ⟶ G)
    {A B : (FiberedCategoryOver.inertia X).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (map F)).map φ ≫
        (FiberedCategoryOver.toNatTrans (map₂ τ)).app B =
      (FiberedCategoryOver.toNatTrans (map₂ τ)).app A ≫
        (FiberedCategoryOver.toFunctor (map G)).map φ := sorry

/-- Two cartesian inertia `2`-morphisms agree when all total-category components agree. -/
@[stacks 04Z4 "cartesian inertia two-cell extensionality"]
theorem ext {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.inertia X).total,
      (FiberedCategoryOver.toNatTrans (map₂ τ)).app A =
        (FiberedCategoryOver.toNatTrans (map₂ σ)).app A) :
    map₂ τ = map₂ σ := sorry

/-- The cartesian inertia action is compatible with left whiskering. -/
@[stacks 04Z4 "cartesian inertia two-cell left whiskering"]
theorem whiskerLeft
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (τ : G ⟶ H) :
    map₂ (F ◁ τ) =
      eqToHom (map.comp F G) ≫
        map F ◁ map₂ τ ≫
          eqToHom (map.comp F H).symm := sorry

/-- The cartesian inertia action is compatible with right whiskering. -/
@[stacks 04Z4 "cartesian inertia two-cell right whiskering"]
theorem whiskerRight
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {F G : X ⟶ Y} (τ : F ⟶ G) (H : Y ⟶ Z) :
    map₂ (τ ▷ H) =
      eqToHom (map.comp F H) ≫
        map₂ τ ▷ map H ≫
          eqToHom (map.comp G H).symm := sorry

end map₂

end FiberedCategoryOver.Inertia

end CategoryTheory
