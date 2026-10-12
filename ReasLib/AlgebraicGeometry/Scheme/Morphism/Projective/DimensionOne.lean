/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison

/-!
# Projectivity of one-dimensional schemes

This file records H-projectivity for proper schemes of dimension at most one over a field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.HProjective

/-- Every proper scheme over a field whose topological Krull dimension is at most one is
H-projective over that field. -/
theorem of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) :
    HProjective f := sorry

end AlgebraicGeometry.HProjective
