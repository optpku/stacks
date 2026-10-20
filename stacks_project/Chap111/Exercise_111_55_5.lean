/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.RankOneLocus
import StacksCheckRecall

/-!
# Rank-one matrices as a locally closed subset of affine 9-space
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AffineSpace

universe u

/- Exercise 111.55.5 (1): over an algebraically closed field, the closed points
of the Zariski locally closed rank-one locus in affine `9`-space are exactly
the points represented by `3 × 3` rank-one matrices. -/
@[stacks 07DJ] #check (AlgebraicGeometry.AffineSpace.closedPoints_rankOneLocus :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    rankOneLocus k ∩ closedPoints (AffineSpaceOverField k 9) =
      closedPointOfMatrix k '' rankOneMatrices k)

/- Exercise 111.55.5 (2): the rank-one locus is irreducible. -/
@[stacks 07DJ] #check (AlgebraicGeometry.AffineSpace.isIrreducible_rankOneLocus :
  ∀ (k : Type u) [Field k] [IsAlgClosed k], IsIrreducible (rankOneLocus k))

/- Exercise 111.55.5 (3): the rank-one locus has dimension `5`. -/
@[stacks 07DJ] #check (AlgebraicGeometry.AffineSpace.topologicalKrullDim_rankOneLocus :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    topologicalKrullDim (rankOneLocus k : Set (AffineSpaceOverField k 9)) = (5 : WithBot ℕ∞))
