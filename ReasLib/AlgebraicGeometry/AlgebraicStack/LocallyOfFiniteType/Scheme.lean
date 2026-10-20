/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The structure morphism of the source scheme of a smooth morphism to an
algebraic stack locally of finite type over `S` is locally of finite type. -/
theorem locallyOfFiniteType_hom_of_smooth {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    AlgebraicGeometry.LocallyOfFiniteType U.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
