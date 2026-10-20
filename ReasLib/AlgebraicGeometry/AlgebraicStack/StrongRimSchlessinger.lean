/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger

/-!
# Algebraic stacks satisfy the strong Rim-Schlessinger condition

An algebraic stack over a scheme satisfies condition (RS*).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- An algebraic stack over a scheme satisfies the strong Rim-Schlessinger condition. -/
instance instHasStrongRimSchlessinger_algebraicStack
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    HasStrongRimSchlessinger X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
