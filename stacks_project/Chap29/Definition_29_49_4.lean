module

public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 29.49.4: for every scheme `X`, the ring `R(X)` consists of rational functions
with the addition and multiplication induced from their dense-open representatives. -/
@[stacks 01RU] #check
  (AlgebraicGeometry.Scheme.rationalFunctionRing : ∀ X : Scheme.{u}, CommRingCat.{u})

#check (AlgebraicGeometry.Scheme.rationalFunctionRingEquivRationalMap :
  ∀ X : Scheme.{u}, AlgebraicGeometry.Scheme.rationalFunctionRing X ≃
    X.RationalMap (Spec (CommRingCat.of
      AlgebraicGeometry.Scheme.RationalFunction.AffineLineRing.{u})))

#check (AlgebraicGeometry.Scheme.rationalFunctionRing_equiv_functionField :
  ∀ (X : Scheme.{u}) [IsIntegral X],
    AlgebraicGeometry.Scheme.rationalFunctionRing X ≃+* X.functionField)
