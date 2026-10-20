/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.QuasiCompact

/-!
# Integrality of reduced irreducible algebraic stacks

A reduced algebraic stack with irreducible space of points is integral if its
absolute diagonal is quasi-compact, in particular if it is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A reduced algebraic stack with irreducible space of points and
quasi-compact absolute diagonal is integral. -/
theorem IsIntegral.of_quasiCompact_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsReduced X] [IsIrreducible X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    IsIntegral X :=
  sorry

/-- A reduced quasi-separated algebraic stack with irreducible space of points
is integral. -/
@[stacks 0GWD]
instance instIsIntegral_of_isQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsReduced X] [IsQuasiSeparated X] [IsIrreducible X] :
    IsIntegral X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
