/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Action

/-!
# Packaged two-cell computations for fibred relative inertia

This leaf exposes the total-category components of the packaged relative-inertia
pseudofunctor.  It lets downstream users work directly with `pseudofunctor.map₂`
and the local hom functor without unfolding either property lift.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}

/-- The total natural transformation underlying the packaged relative-inertia
`2`-cell is the total transformation of the explicit action. -/
@[simp]
theorem pseudofunctor.map₂.toNatTrans
    {f g : S ⟶ T} (eta : f ⟶ g) :
    FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ eta) =
      FiberedCategoryOver.toNatTrans
        (FiberedCategoryOver.RelativeInertia.pseudoComma.map₂ eta) := sorry

/-- A component of the packaged relative-inertia `2`-cell is the explicit
intertwining component. -/
@[simp]
theorem pseudofunctor.map₂.app
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ eta)).app A =
      map₂.component eta A := sorry

/-- Every component of the packaged relative-inertia `2`-cell is vertical over
the identity of its base object. -/
theorem pseudofunctor.map₂.app.isHomLift
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ eta)).app A) := sorry

/-- The arrow underlying a packaged relative-inertia `2`-cell component is the
left endpoint component of the original pseudo-comma `2`-morphism. -/
@[simp]
theorem pseudofunctor.map₂.app.underlying
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).map₂ eta)).app A) =
      (FiberedCategoryOver.toNatTrans
        (Bicategory.PseudoComma.left₂ eta)).app A.obj := sorry

/-- Packaged relative-inertia `2`-cell components are natural in total-category
morphisms. -/
@[reassoc]
theorem pseudofunctor.map₂.naturality
    {f g : S ⟶ T} (eta : f ⟶ g)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor ((pseudofunctor C).map f)).map phi ≫
        (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ eta)).app B =
      (FiberedCategoryOver.toNatTrans ((pseudofunctor C).map₂ eta)).app A ≫
        (FiberedCategoryOver.toFunctor ((pseudofunctor C).map g)).map phi := sorry

/-- The total natural transformation obtained from the local hom functor is the
same explicit relative-inertia action. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.toNatTrans
    {f g : S ⟶ T} (eta : f ⟶ g) :
    FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor S T |>.map eta) =
      FiberedCategoryOver.toNatTrans
        (FiberedCategoryOver.RelativeInertia.pseudoComma.map₂ eta) := sorry

/-- Evaluation of the local hom functor on a `2`-cell gives the explicit
relative-inertia component. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.app
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.toNatTrans
      ((pseudofunctor C).mapFunctor S T |>.map eta)).app A =
        map₂.component eta A := sorry

/-- The arrow underlying a local-hom component is the left endpoint component
of the original pseudo-comma `2`-morphism. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.app.underlying
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor S T |>.map eta)).app A) =
      (FiberedCategoryOver.toNatTrans
        (Bicategory.PseudoComma.left₂ eta)).app A.obj := sorry

/-- Every relative local-hom component is vertical over the identity on its base object. -/
theorem pseudofunctor.mapFunctor.map.app.isHomLift
    {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor S T |>.map eta)).app A) := sorry

/-- Relative local-hom components are natural in total-category arrows. -/
@[reassoc]
theorem pseudofunctor.mapFunctor.map.naturality
    {f g : S ⟶ T} (eta : f ⟶ g)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor
      ((pseudofunctor C).mapFunctor S T |>.obj f)).map phi ≫
        (FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor S T |>.map eta)).app B =
      (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor S T |>.map eta)).app A ≫
        (FiberedCategoryOver.toFunctor
          ((pseudofunctor C).mapFunctor S T |>.obj g)).map phi := sorry

/-- Relative local-hom `2`-cells agree when all total-category components agree. -/
theorem pseudofunctor.mapFunctor.map.ext
    {f g : S ⟶ T} {eta theta : f ⟶ g}
    (h : ∀ A : (FiberedCategoryOver.relativeInertia S.hom).total,
      (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapFunctor S T |>.map eta)).app A =
        (FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapFunctor S T |>.map theta)).app A) :
    ((pseudofunctor C).mapFunctor S T).map eta =
      ((pseudofunctor C).mapFunctor S T).map theta := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
