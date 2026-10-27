/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.PointSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleQuotient

/-!
# Dimension of the infinite-product quotient

Over a finite field, the infinite-product quotient has étale-local dimension zero
everywhere. Its presentation-level point space has topological Krull dimension one,
with local dimension zero at its generic point and one elsewhere.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

/-- The infinite-product cover over a finite field has local topological Krull
dimension zero at every point. -/
theorem topologicalKrullDimAt_cover_eq_zero (k : Type u) [Field k] [Fintype k]
    (u : (cover k).left) : topologicalKrullDimAt u = 0 :=
  sorry

/-- The algebraic-space quotient of the infinite-product étale equivalence relation
over a finite field has dimension zero at every point. -/
theorem dimensionAt_eq_zero (k : Type u) [Field k] [Fintype k]
    (x : Points ((preRelation k).etaleQuotientSpace)) : dimensionAt x = 0 :=
  sorry

/-- The presentation-level point space of the infinite-product quotient over a finite
field has topological Krull dimension one. -/
theorem topologicalKrullDim_spacePoints_eq_one (k : Type u) [Field k] [Fintype k] :
    topologicalKrullDim (spacePoints k) = 1 :=
  sorry

/-- Away from its generic point, the presentation-level point space of the
infinite-product quotient over a finite field has local topological Krull dimension one. -/
theorem topologicalKrullDimAt_spacePoints_eq_one (k : Type u) [Field k] [Fintype k]
    {x : spacePoints k} (hx : x ≠ genericPoint k) : topologicalKrullDimAt x = 1 :=
  sorry

/-- The generic point of the presentation-level point space of the infinite-product
quotient over a finite field has local topological Krull dimension zero. -/
theorem topologicalKrullDimAt_genericPoint_eq_zero (k : Type u) [Field k] [Fintype k] :
    topologicalKrullDimAt (genericPoint k) = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteProduct
