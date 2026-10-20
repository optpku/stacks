/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
import StacksCheckRecall

/-!
# Function fields of good integral algebraic spaces

In Situation 82.2.1, if `X / B` is good and `X` is integral, the function field
`R(X)` is the residue field at the generic point of `X`. For any point `x`,
`κ(x)` is the function field of the unique integral closed subspace through `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 82.7.3: in Situation 82.2.1, the function field of a good integral
algebraic space is its residue field at the generic point. Every point `x` is
the generic point of a unique integral closed subspace `Z`. Its inclusion is
monomorphic by `ClosedSubspace.spec`, and the generic point of `Z.X` maps to `x`.
The following comparison applied to that inclusion therefore identifies
`RationalFunction Z.X` with the ambient residue field at `x`. The companion
checks retain the field structure, generic-point comparison, and full uniqueness
of the integral closed subspace over the ambient space. -/
@[stacks 0ENX] #check
  (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRingEquivResidueFieldOfMono :
    ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} [IsIntegral Y] [IsDecent X]
      (i : Y ⟶ X) [Mono i] {η : Points Y}, η ∈ genericPoints Y →
      RationalFunction Y ≃+* ULift.{u + 1} (X.residueField (Points.map i η)))

#check (AlgebraicGeometry.AlgebraicSpace.instField_rationalFunctionRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X],
    Field (RationalFunction X))

#check (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRingEquivResidueField :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X}, η ∈ genericPoints X →
    RationalFunction X ≃+* ULift.{u + 1} (X.residueField η))

#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_integralClosedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (ξ : Points X),
    ∃ Z : ClosedSubspace X,
      IsIntegral Z.X ∧ IsGenericPoint ξ Z.pointsSet ∧
        ∀ (Z' : ClosedSubspace X), IsIntegral Z'.X → IsGenericPoint ξ Z'.pointsSet →
          ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι)

end AlgebraicGeometry.AlgebraicSpace
