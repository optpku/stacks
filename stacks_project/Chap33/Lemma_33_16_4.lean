/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.16.4: for every morphism `f : X ⟶ S` and point `x : X`, the relative tangent
space is canonically linearly equivalent over `κ(x)` to the `𝒪_{X,x}`-linear dual of
the Kähler differentials of the induced map on stalks. -/
@[stacks 0B2D] #check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceLinearDual :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x ≃ₗ[X.residueField x]
        (CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.presheaf.stalk x]
          X.residueField x))
