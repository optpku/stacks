/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.NoetherNormalization

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.18.4: let `f : X ⟶ S` be a finite type morphism of affine schemes and let
`x : X`. If `r` is the dimension of the relative tangent space at `x`, then `f` factors through
relative affine `r`-space over `S` by a morphism that is unramified at `x`. -/
@[stacks 0CBK] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineSpace_factorization_unramifiedAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] [Scheme.Hom.FiniteType f]
      (x : X),
      let r := Module.finrank (X.residueField x) (Scheme.Hom.tangentSpaceAt f x)
      let A := AffineSpace (ULift.{u} (Fin r)) S
      ∃ π : X ⟶ A, π ≫ (A ↘ S) = f ∧ π.UnramifiedAt x)
