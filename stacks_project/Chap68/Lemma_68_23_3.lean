/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Jacobson
import StacksCheckRecall

/-!
# Finite-type points of decent Jacobson algebraic spaces

On a decent Jacobson algebraic space, the finite-type points are exactly the
closed points of the space of points.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.23.3: Let `S` be a scheme. Let `X` be a decent Jacobson algebraic space
over `S`. Then `finiteTypePoints X` is the set of closed points of `Points X`. -/
@[stacks 0BA5] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteTypePoints_eq_closedPoints :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] [IsJacobson X],
      finiteTypePoints X = closedPoints (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_finiteTypePoints_iff_mem_closedPoints :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] [IsJacobson X] {x : Points X},
    x ∈ finiteTypePoints X ↔ x ∈ closedPoints (Points X))
