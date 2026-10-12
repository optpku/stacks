/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Intersections in projective space

Dimension and nonemptiness results for intersections of closed subsets of standard projective
space.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- If two nonempty closed subsets of projective `n`-space have dimensions `r` and `s` with
`r + s ≥ n`, then their intersection has dimension at least `r + s - n`. -/
theorem closedSubset_inter_dim_ge_add_sub_of_dim_add_ge
    {k : Type u} [Field k] {n r s : ℕ}
    (X Y : TopologicalSpace.Closeds (scheme k n))
    (hXne : (X : Set (scheme k n)).Nonempty)
    (hYne : (Y : Set (scheme k n)).Nonempty)
    (hXdim : topologicalKrullDim (X : Set (scheme k n)) = r)
    (hYdim : topologicalKrullDim (Y : Set (scheme k n)) = s)
    (hadd : r + s ≥ n) :
    topologicalKrullDim
      ((X ⊓ Y : TopologicalSpace.Closeds (scheme k n)) : Set (scheme k n)) ≥ r + s - n := sorry

/-- Two nonempty closed subsets of projective `n`-space whose dimensions sum to at least `n`
have nonempty intersection. -/
theorem closedSubset_inter_nonempty_of_dim_add_ge
    {k : Type u} [Field k] {n r s : ℕ}
    (X Y : TopologicalSpace.Closeds (scheme k n))
    (hXne : (X : Set (scheme k n)).Nonempty)
    (hYne : (Y : Set (scheme k n)).Nonempty)
    (hXdim : topologicalKrullDim (X : Set (scheme k n)) = r)
    (hYdim : topologicalKrullDim (Y : Set (scheme k n)) = s)
    (hadd : r + s ≥ n) :
    ((X ⊓ Y : TopologicalSpace.Closeds (scheme k n)) : Set (scheme k n)).Nonempty := sorry

end AlgebraicGeometry.ProjectiveSpace
