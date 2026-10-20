/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- For a gerbe morphism of algebraic stacks, quasi-compactness of the object
diagonal of the source implies quasi-compactness of the object diagonal of the
target. -/
@[stacks 0DQL]
theorem diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f]
    [QuasiCompact (diagonal.{u + 1, u, u + 1} X)] :
    QuasiCompact (diagonal.{u + 1, u, u + 1} Y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
