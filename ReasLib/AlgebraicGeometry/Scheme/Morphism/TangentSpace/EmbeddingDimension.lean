/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.EmbeddingDimension

/-!
# Tangent dimension and embedding dimension

This module defines relative tangent dimension and compares it with intrinsic
embedding dimension at closed points over an algebraically closed field.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

/-- The tangent dimension of a scheme morphism at a point is the residue-field dimension of its
relative tangent space. -/
@[stacks 0C2H]
noncomputable abbrev tangentDimensionAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : ℕ :=
  Module.finrank (X.residueField x) (relativeTangentSpaceAt f x)

end

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SchemeOverField

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- At a closed point of a locally algebraic scheme over an algebraically closed field, the
relative tangent dimension equals the intrinsic embedding dimension. -/
theorem tangentDimensionAt_eq_embeddingDimensionAt_of_closedPoint
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (x : X.left) (hx : IsClosed {x}) :
    Scheme.Hom.tangentDimensionAt X.hom x = Scheme.embeddingDimensionAt x := sorry

end


end AlgebraicGeometry.SchemeOverField
