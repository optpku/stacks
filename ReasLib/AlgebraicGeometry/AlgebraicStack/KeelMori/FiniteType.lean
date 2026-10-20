/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Locally of finite type for moduli spaces

A locally-of-finite-type morphism from an algebraic stack with finite inertia
to a locally Noetherian algebraic space induces a locally-of-finite-type
morphism from its uniform categorical moduli space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A locally-of-finite-type morphism from an algebraic stack with finite
inertia to a locally Noetherian algebraic space induces a locally-of-finite-type
morphism from any uniform categorical moduli space through which it factors
up to a 2-isomorphism. -/
theorem locallyOfFiniteType_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y M : AlgebraicSpace S} [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    [AlgebraicSpace.IsLocallyNoetherian Y] (p : X ⟶ Y.toGroupoids)
    [AlgebraicStack.LocallyOfFiniteType p] (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] (q : M ⟶ Y)
    (α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p) :
    AlgebraicSpace.LocallyOfFiniteType q :=
  sorry

end AlgebraicGeometry.AlgebraicStack
