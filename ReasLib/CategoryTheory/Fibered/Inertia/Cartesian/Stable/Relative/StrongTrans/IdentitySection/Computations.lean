/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.StrongTrans.IdentitySection.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps

/-!
# Computations for the stable relative-inertia identity section

The component formulas are exposed through the neutral fibred relative-inertia API, so downstream
arguments can remain at the canonical `toFunctor` or `toBasedFunctor` level.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans

variable {C : Type u} [Category.{v} C]

variable
    {S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))}

/-- The stable relative-inertia identity-section component is canonical. -/
@[simp]
theorem app :
    (FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans C).app S =
      FiberedCategoryOver.RelativeInertia.identitySection S.hom := sorry

/-- The underlying based functor of the stable identity-section component is neutral. -/
@[simp]
theorem app.toBasedFunctor :
    FiberedCategoryOver.toBasedFunctor
        ((FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans C).app S) =
      BasedCategory.RelativeInertia.identitySection
        (FiberedCategoryOver.toBasedFunctor S.hom) := sorry

/-- The total functor of the stable identity-section component is neutral. -/
@[simp]
theorem app.toFunctor :
    FiberedCategoryOver.toFunctor
        ((FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans C).app S) =
      CategoryTheory.RelativeInertia.identitySection
        (FiberedCategoryOver.toFunctor S.hom) := sorry

/-- The identity section fixes the underlying object of every left-endpoint object. -/
@[simp]
theorem app_obj
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).obj S).total) :
    ((FiberedCategoryOver.toFunctor
      ((FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans C).app S)).obj x).obj =
      x := sorry

/-- The identity section chooses the identity automorphism. -/
@[simp]
theorem app_aut
    (x : ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).obj S).total) :
    ((FiberedCategoryOver.toFunctor
      ((FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans C).app S)).obj x).aut =
      1 := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma.identitySection.strongTrans

end CategoryTheory
