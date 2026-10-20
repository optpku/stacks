/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger

/-!
# Algebraic stacks satisfy the Rim-Schlessinger condition

An algebraic stack over a locally Noetherian scheme satisfies condition (RS).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- An algebraic stack over a locally Noetherian scheme satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_algebraicStack {S : Scheme.{u}}
    [IsLocallyNoetherian S] (X : GroupoidsOver S) [AlgebraicStack X] :
    HasRimSchlessinger X := sorry

end AlgebraicGeometry.GroupoidsOver
