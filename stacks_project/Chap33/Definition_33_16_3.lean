/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic

@[expose] public section

open CategoryTheory

universe u

/- Definition 33.16.3: for a morphism of schemes `f : X ⟶ S` and a point `x : X`, the tangent
space of `X` over `S` at `x` is the canonical `κ(x)`-vector space of relative tangent vectors. -/
@[stacks 0B2C] #check
  (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X), Type u)

#check
  (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt_def :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x =
        AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceAt f x)

#check
  (AlgebraicGeometry.Scheme.Hom.tangentSpaceAtModule :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      Module (X.residueField x) (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x))
