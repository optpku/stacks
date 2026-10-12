/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

#check (ChowMotive.exactPairing :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    (d : ℕ), topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ExactPairing (ChowMotive.h X) (ChowMotive.tateTwist X d))
