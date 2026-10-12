/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.Descent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The target of a surjective universally closed morphism from an affine scheme is affine. -/
theorem isAffine_of_surjective_universallyClosed
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [UniversallyClosed f] [IsAffine X] :
    IsAffine S := sorry

end AlgebraicGeometry.Scheme
