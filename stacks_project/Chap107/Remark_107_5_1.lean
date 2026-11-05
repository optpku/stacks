/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
import StacksCheckRecall

/-!
# Dimension of an algebraic space versus its underlying topological space

Étale-local dimension need not agree with the local topological Krull dimension of
the space of points. The two standard counterexamples are `𝔸¹_k / ℤ` and the infinite
product algebraic space of Example 65.14.9; they do agree on decent algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/- Remark 107.5.1 (1): if `k` is a field of characteristic zero and `X = space k` is the
algebraic space `𝔸¹_k / ℤ`, then `dimensionAt x = 1` at every point `x` of `X`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.dimensionAt_eq_one :
    ∀ (k : Type u) [Field k] [CharZero k] (x : Points (space k)), dimensionAt x = 1)

/- Remark 107.5.1 (2): the underlying topological space `Points (space k)` of `𝔸¹_k / ℤ`
carries the indiscrete topology. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.instIndiscreteTopology_points :
    ∀ (k : Type u) [Field k] [CharZero k], IndiscreteTopology (Points (space k)))

/- Remark 107.5.1 (3): the underlying topological space `Points (space k)` of `𝔸¹_k / ℤ`
has topological Krull dimension `0`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.topologicalKrullDim_points_eq_zero :
    ∀ (k : Type u) [Field k] [CharZero k], topologicalKrullDim (Points (space k)) = 0)

/- Remark 107.5.1 (4): at every point `x` of `Points (space k)`, the local topological
Krull dimension is `0`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.topologicalKrullDimAt_points_eq_zero :
    ∀ (k : Type u) [Field k] [CharZero k]
    (x : Points (space k)), topologicalKrullDimAt x = 0)

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

/- Remark 107.5.1 (5): in Algebraic Spaces, Example 65.14.9, the étale cover `U = cover k`
has local topological Krull dimension `0` at every point, so the algebraic space is of
dimension `0` at each of its points. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.topologicalKrullDimAt_cover_eq_zero :
    ∀ (k : Type u) [Field k] [Fintype k]
    (u : (cover k).left), topologicalKrullDimAt u = 0)

/- Remark 107.5.1 (5): the algebraic space of the infinite-product quotient has
étale-local dimension zero at every point. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.dimensionAt_eq_zero :
    ∀ (k : Type u) [Field k] [Fintype k]
    (x : Points (space k)), dimensionAt x = 0)

/- Remark 107.5.1 (6): the canonical point space `Points (space k)` is of
topological Krull dimension `1`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.topologicalKrullDim_points_eq_one :
    ∀ (k : Type u) [Field k] [Fintype k], topologicalKrullDim (Points (space k)) = 1)

/- Remark 107.5.1 (7): off the generic point, the local topological Krull dimension of
`Points (space k)` is `1`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.topologicalKrullDimAt_points_eq_one :
    ∀ (k : Type u) [Field k] [Fintype k]
    {x : Points (space k)} (hx : x ≠ spaceGenericPoint k), topologicalKrullDimAt x = 1)

/- Remark 107.5.1 (7), corrected generic-point case: the local topological Krull
dimension at the generic point is zero. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.topologicalKrullDimAt_spaceGenericPoint_eq_zero :
    ∀ (k : Type u) [Field k] [Fintype k], topologicalKrullDimAt (spaceGenericPoint k) = 0)

/- Remark 107.5.1 (8): `|X|` is irreducible. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instIrreducibleSpace_points :
    ∀ (k : Type u) [Field k] [Fintype k], IrreducibleSpace (Points (space k)))

/- Remark 107.5.1 (9): `|X|` admits a generic point. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.isGenericPoint_spaceGenericPoint :
    ∀ (k : Type u) [Field k] [Fintype k], IsGenericPoint (spaceGenericPoint k) Set.univ)

end AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 107.5.1 (10): on a decent algebraic space, étale-local dimension agrees with
the local topological Krull dimension of `|X|`. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.dimensionAt_eq_topologicalKrullDimAt_of_isDecent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
      dimensionAt x = topologicalKrullDimAt x)

/- Remark 107.5.1 (11): a quasi-separated algebraic space is decent. -/
@[stacks 0DRF] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_isQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiSeparated X], IsDecent X)

end AlgebraicGeometry.AlgebraicSpace
