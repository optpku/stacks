/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/-- If a nonempty Noetherian scheme has finite topological Krull dimension `d`, then its affine
stratification number is at most `d`. -/
theorem number_le_of_topologicalKrullDim_eq {X : Scheme.{u}} [Nonempty X]
    [IsNoetherian X] (d : ℕ)
    (h_dim : topologicalKrullDim X = (d : WithBot ℕ∞)) : number X ≤ d := sorry

end AlgebraicGeometry.Scheme.FiniteAffineStratification
