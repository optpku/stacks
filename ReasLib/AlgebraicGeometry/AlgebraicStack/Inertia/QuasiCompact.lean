/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.BaseChange

/-!
# Quasi-compact inertia of quasi-separated algebraic stacks

The canonical inertia projection of a quasi-separated algebraic stack is
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The inertia morphism `I_X ⟶ X` of a quasi-separated algebraic stack is
quasi-compact. -/
instance instQuasiCompact_forget_of_isQuasiSeparated {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiSeparated X] :
    QuasiCompact (forget.{u + 1, u, u, u + 1} X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
