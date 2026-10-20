/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
import StacksCheckRecall

/-!
# Closed points via residual spaces

On a locally Noetherian algebraic space, a point is closed if and only if its
residual-space monomorphism is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.13.12: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x ∈ |X|` with residual space `Z ⊂ X`. Assume `X` is locally Noetherian.
Then `x` is a closed point of `|X|` if and only if the morphism `Z ⟶ X` is a
closed immersion. -/
@[stacks 0H1U] #check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.mem_closedPoints_iff_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
      {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x],
      x ∈ closedPoints (Points X) ↔ IsClosedImmersion ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.mem_closedPoints :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x] [IsClosedImmersion ι],
    x ∈ closedPoints (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.isClosedImmersion_of_mem_closedPoints :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x]
    (hx : x ∈ closedPoints (Points X)), IsClosedImmersion ι)
