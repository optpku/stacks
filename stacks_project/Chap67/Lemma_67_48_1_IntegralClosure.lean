module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.IntegralClosure
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Integral closure of a quasi-coherent algebra

The locally integral subalgebra and its inclusion are available from their mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.integralClosure :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.QcAlgebraUnder → X.QcAlgebraUnder)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.inclusion :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    integralClosure A ⟶ A)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.locallyIntegral_eq_integralClosure :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (U : affineEtaleSite X),
    locallyIntegral A U.obj =
      _root_.integralClosure Γ(U.obj.left.left, ⊤) (sectionRing A U.obj))
