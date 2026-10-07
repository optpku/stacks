module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Strict.Action

/-!
# Packaged two-cell computations for strict fibred inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The total natural transformation underlying a strict fibred-inertia
`2`-cell is the explicit action. -/
@[simp]
theorem strictPseudofunctor.map₂.toNatTrans {F G : X ⟶ Y} (tau : F ⟶ G) :
    FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau) =
      FiberedCategoryOver.toNatTrans (FiberedCategoryOver.Inertia.map₂ tau) := sorry

/-- A strict packaged `2`-cell evaluates to the neutral inertia component. -/
@[simp]
theorem strictPseudofunctor.map₂.app {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.toBasedNatTrans tau) A := sorry

/-- Every strict packaged component is vertical over the identity on its base
object. -/
theorem strictPseudofunctor.map₂.app.isHomLift {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app A) := sorry

/-- The arrow underlying a strict packaged component is the original total
category component. -/
@[simp]
theorem strictPseudofunctor.map₂.app.underlying {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app A) =
      (FiberedCategoryOver.toNatTrans tau).app A.obj := sorry

/-- Strict packaged components are natural in total-category arrows. -/
@[reassoc]
theorem strictPseudofunctor.map₂.naturality {F G : X ⟶ Y} (tau : F ⟶ G)
    {A B : (FiberedCategoryOver.inertia X).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor ((strictPseudofunctor C).map F)).map phi ≫
        (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app B =
      (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app A ≫
        (FiberedCategoryOver.toFunctor ((strictPseudofunctor C).map G)).map phi := sorry

/-- Two strict packaged `2`-cells agree when all total-category components
agree. -/
theorem strictPseudofunctor.map₂.ext {F G : X ⟶ Y} {tau sigma : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.inertia X).total,
      (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ tau)).app A =
        (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).map₂ sigma)).app A) :
    (strictPseudofunctor C).map₂ tau = (strictPseudofunctor C).map₂ sigma := sorry

/-- The total natural transformation obtained from the strict local hom functor is
the explicit strict inertia action. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map.toNatTrans
    {F G : X ⟶ Y} (tau : F ⟶ G) :
    FiberedCategoryOver.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map tau) =
      FiberedCategoryOver.toNatTrans
        (FiberedCategoryOver.Inertia.map₂ tau) := sorry

/-- A strict local-hom component is the explicit neutral inertia component. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map.app
    {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans
      ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app A =
        BasedCategory.Inertia.map₂.component
          (FiberedCategoryOver.toBasedNatTrans tau) A := sorry

/-- Every strict local-hom component is vertical over the identity on its base object. -/
theorem strictPseudofunctor.mapFunctor.map.app.isHomLift
    {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app A) := sorry

/-- The arrow underlying a strict local-hom component is the original component. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map.app.underlying
    {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app A) =
      (FiberedCategoryOver.toNatTrans tau).app A.obj := sorry

/-- Strict local-hom components are natural in total-category arrows. -/
@[reassoc]
theorem strictPseudofunctor.mapFunctor.map.naturality
    {F G : X ⟶ Y} (tau : F ⟶ G)
    {A B : (FiberedCategoryOver.inertia X).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor
      ((strictPseudofunctor C).mapFunctor X Y |>.obj F)).map phi ≫
        (FiberedCategoryOver.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app B =
      (FiberedCategoryOver.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app A ≫
        (FiberedCategoryOver.toFunctor
          ((strictPseudofunctor C).mapFunctor X Y |>.obj G)).map phi := sorry

/-- Strict local-hom `2`-cells agree when all total-category components agree. -/
theorem strictPseudofunctor.mapFunctor.map.ext
    {F G : X ⟶ Y} {tau sigma : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.inertia X).total,
      (FiberedCategoryOver.toNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map tau)).app A =
        (FiberedCategoryOver.toNatTrans
          ((strictPseudofunctor C).mapFunctor X Y |>.map sigma)).app A) :
    ((strictPseudofunctor C).mapFunctor X Y).map tau =
      ((strictPseudofunctor C).mapFunctor X Y).map sigma := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
