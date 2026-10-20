/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.Action

/-!
# Packaged two-cell computations for fibred inertia

This leaf exposes the total-category view of the packaged absolute-inertia
`2`-cell action and its local hom functor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The total natural transformation underlying packaged fibred inertia is
the total transformation of the explicit action. -/
@[simp]
theorem pseudofunctor.map₂.toNatTrans {F G : X ⟶ Y} (tau : F ⟶ G) :
    FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau) =
      FiberedCategoryOver.toNatTrans
        (FiberedCategoryOver.Inertia.map₂ tau) := sorry

/-- A component of packaged fibred inertia is the explicit neutral inertia
component. -/
@[simp]
theorem pseudofunctor.map₂.app {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.toBasedNatTrans tau) A := sorry

/-- Every packaged fibred-inertia component is vertical over the identity on
the base object. -/
theorem pseudofunctor.map₂.app.isHomLift {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app A) := sorry

/-- The arrow underlying a packaged fibred-inertia component is the original
total-category component. -/
@[simp]
theorem pseudofunctor.map₂.app.underlying {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app A) =
      (FiberedCategoryOver.toNatTrans tau).app A.obj := sorry

/-- Packaged fibred-inertia components are natural in total-category arrows. -/
@[reassoc]
theorem pseudofunctor.map₂.naturality {F G : X ⟶ Y} (tau : F ⟶ G)
    {A B : (FiberedCategoryOver.inertia X).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor ((pseudofunctor C).map F)).map phi ≫
        (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app B =
      (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app A ≫
        (FiberedCategoryOver.toFunctor ((pseudofunctor C).map G)).map phi := sorry

/-- Two packaged fibred-inertia `2`-cells agree when all total-category
components agree. -/
theorem pseudofunctor.map₂.ext {F G : X ⟶ Y} {tau sigma : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.inertia X).total,
      (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ tau)).app A =
        (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ sigma)).app A) :
    (pseudofunctor C).map₂ tau = (pseudofunctor C).map₂ sigma := sorry

/-- The packaged local hom action has the same total natural transformation
as the explicit inertia action. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.toNatTrans {F G : X ⟶ Y} (tau : F ⟶ G) :
    FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map tau) =
      FiberedCategoryOver.toNatTrans (FiberedCategoryOver.Inertia.map₂ tau) := sorry

/-- Evaluating the packaged local hom action gives the explicit neutral
inertia component. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.app {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans
      ((pseudofunctor C).mapFunctor X Y |>.map tau)).app A =
        BasedCategory.Inertia.map₂.component
          (FiberedCategoryOver.toBasedNatTrans tau) A := sorry

/-- Every ordinary local-hom component is vertical over the identity on its base object. -/
theorem pseudofunctor.mapFunctor.map.app.isHomLift
    {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Y).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map tau)).app A) := sorry

/-- The arrow underlying an ordinary local-hom component is the original component. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.app.underlying
    {F G : X ⟶ Y} (tau : F ⟶ G)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map tau)).app A) =
      (FiberedCategoryOver.toNatTrans tau).app A.obj := sorry

/-- Ordinary local-hom components are natural in total-category arrows. -/
@[reassoc]
theorem pseudofunctor.mapFunctor.map.naturality
    {F G : X ⟶ Y} (tau : F ⟶ G)
    {A B : (FiberedCategoryOver.inertia X).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor
      ((pseudofunctor C).mapFunctor X Y |>.obj F)).map phi ≫
        (FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map tau)).app B =
      (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map tau)).app A ≫
        (FiberedCategoryOver.toFunctor
          ((pseudofunctor C).mapFunctor X Y |>.obj G)).map phi := sorry

/-- Ordinary local-hom `2`-cells agree when all total-category components agree. -/
theorem pseudofunctor.mapFunctor.map.ext
    {F G : X ⟶ Y} {tau sigma : F ⟶ G}
    (h : ∀ A : (FiberedCategoryOver.inertia X).total,
      (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map tau)).app A =
        (FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor X Y |>.map sigma)).app A) :
    ((pseudofunctor C).mapFunctor X Y).map tau =
      ((pseudofunctor C).mapFunctor X Y).map sigma := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
