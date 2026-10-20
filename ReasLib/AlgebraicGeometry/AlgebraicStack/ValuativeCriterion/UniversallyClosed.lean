/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-!
# Valuative criterion for universal closedness

A quasi-compact morphism of algebraic stacks that satisfies the existence part
of the valuative criterion is universally closed.
A quasi-separated universally closed morphism of algebraic stacks satisfies
the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-- A quasi-compact morphism of algebraic stacks that satisfies the existence
part of the valuative criterion is universally closed. -/
@[stacks 0CLW]
instance of_quasiCompact_of_existence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [ValuativeCriterion.Existence f] : UniversallyClosed f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyClosed

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- A quasi-separated universally closed morphism of algebraic stacks satisfies
the existence part of the valuative criterion. -/
@[stacks 0CLX]
instance Existence.of_universallyClosed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] [UniversallyClosed f] : Existence f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
