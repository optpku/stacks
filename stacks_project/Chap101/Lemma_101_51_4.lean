/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.ClosedImmersion
import StacksCheckRecall

/-!
# Closed points via residual gerbes

On a locally Noetherian algebraic stack, a point is closed if and only if its
residual-gerbe monomorphism is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Groupoids.Hom (ClosedImmersion)
open scoped Bicategory

universe u

/- Lemma 101.51.4: Let `X` be a locally Noetherian algebraic stack. Let
`x ∈ |X|` with residual gerbe `ι : Z ⟶ X` (Lemma 101.31.3). Then `x` is a
closed point of `|X|` if and only if `ι` is a closed immersion. -/
@[stacks 0H27] #check
  (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.mem_closedPoints_iff_closedImmersion :
    ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
      [IsLocallyNoetherian X] {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x],
      x ∈ closedPoints (Points X) ↔ ClosedImmersion ι)

/- If a residual-gerbe monomorphism is a closed immersion, then the marked
point is a closed point of `|X|`. -/
#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.mem_closedPoints :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] [ClosedImmersion ι],
    x ∈ closedPoints (Points X))
