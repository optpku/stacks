/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Projections

/-!
# Action computations for fibred relative inertia

This leaf identifies the `1`-morphism, `2`-morphism, and local-hom fields of
the fibred relative-inertia pseudofunctor with their explicit reusable owners.
It also records the whiskering formulas for the explicit `2`-cell action.
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

/-- Fibred relative inertia maps a square by the canonical explicit relative
inertia map. -/
@[simp]
theorem pseudofunctor.map (f : S ⟶ T) :
    (pseudofunctor C).map f = map f := sorry

/-- The based functor underlying fibred relative inertia is the neutral
pseudo-comma relative-inertia map. -/
@[simp]
theorem pseudofunctor.map.toBasedFunctor (f : S ⟶ T) :
    FiberedCategoryOver.toBasedFunctor ((pseudofunctor C).map f) =
      BasedCategory.RelativeInertia.map
        (FiberedCategoryOver.toBasedFunctor
          (Bicategory.PseudoComma.left f))
        (FiberedCategoryOver.toBasedFunctor
          (Bicategory.PseudoComma.right f))
        (FiberedCategoryOver.toBasedFunctorIso
          (Bicategory.PseudoComma.cellIso f).symm) := sorry

/-- Fibred relative inertia acts on `2`-morphisms by the explicit
left-endpoint action on relative-inertia objects. -/
@[simp]
theorem pseudofunctor.map₂ {f g : S ⟶ T} (η : f ⟶ g) :
    (pseudofunctor C).map₂ η = map₂ η := sorry

/-- The based natural transformation underlying the fibred relative-inertia
`2`-cell is the explicit local based action. -/
@[simp]
theorem pseudofunctor.map₂.toBasedNatTrans
    {f g : S ⟶ T} (η : f ⟶ g) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).map₂ η) =
      map₂.basedNatTrans η := sorry

/-- The local action of fibred relative inertia is the explicit hom functor
on pseudo-comma squares. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (pseudofunctor C).mapFunctor S T = mapFunctor S T := sorry

/-- Evaluating the fibred relative-inertia local hom functor on a `1`-cell
gives the canonical explicit relative-inertia map. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj (f : S ⟶ T) :
    ((pseudofunctor C).mapFunctor S T).obj f =
      FiberedCategoryOver.RelativeInertia.pseudoComma.map f := sorry

/-- Evaluating the fibred relative-inertia local hom functor on a `2`-cell
gives the canonical explicit relative-inertia action. -/
@[simp]
theorem pseudofunctor.mapFunctor.map {f g : S ⟶ T} (η : f ⟶ g) :
    ((pseudofunctor C).mapFunctor S T).map η =
      FiberedCategoryOver.RelativeInertia.pseudoComma.map₂ η := sorry

/-- Evaluating the fibred relative-inertia local hom functor on a `1`-cell
gives the neutral pseudo-comma map at the based level. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj.toBasedFunctor (f : S ⟶ T) :
    FiberedCategoryOver.toBasedFunctor
        ((pseudofunctor C).mapFunctor S T |>.obj f) =
      BasedCategory.RelativeInertia.map
        (FiberedCategoryOver.toBasedFunctor
          (Bicategory.PseudoComma.left f))
        (FiberedCategoryOver.toBasedFunctor
          (Bicategory.PseudoComma.right f))
        (FiberedCategoryOver.toBasedFunctorIso
          (Bicategory.PseudoComma.cellIso f).symm) := sorry

/-- Evaluating the fibred relative-inertia local hom functor on a `2`-cell
gives the explicit based local action. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.toBasedNatTrans
    {f g : S ⟶ T} (η : f ⟶ g) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapFunctor S T |>.map η) =
      map₂.basedNatTrans η := sorry

/-- The explicit fibred relative-inertia action carries left whiskering
through the composition comparisons of its packaged pseudofunctor. -/
theorem map₂.whiskerLeft
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) {g h : S ⟶ T} (η : g ⟶ h) :
    map₂ (f ◁ η) =
      ((pseudofunctor C).mapComp f g).hom ≫
        map f ◁ map₂ η ≫
          ((pseudofunctor C).mapComp f h).inv := sorry

/-- The explicit fibred relative-inertia action carries right whiskering
through the composition comparisons of its packaged pseudofunctor. -/
theorem map₂.whiskerRight
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    {f g : R ⟶ S} (η : f ⟶ g) (h : S ⟶ T) :
    map₂ (η ▷ h) =
      ((pseudofunctor C).mapComp f h).hom ≫
        map₂ η ▷ map h ≫
          ((pseudofunctor C).mapComp g h).inv := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
