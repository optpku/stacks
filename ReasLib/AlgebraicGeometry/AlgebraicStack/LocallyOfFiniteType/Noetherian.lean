/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Locally of finite type over locally Noetherian algebraic stacks

A morphism of algebraic stacks that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- The source of a locally-of-finite-type morphism of algebraic stacks with
locally Noetherian target is locally Noetherian. -/
@[stacks 06R6]
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
