module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.IntegralClosure
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 67.48.1. Every quasi-coherent algebra on an algebraic space contains a
quasi-coherent subalgebra whose sections on each affine étale chart are exactly the
integral closure of the structure ring inside the original section algebra. -/
@[stacks 0820] #check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.exists_integralClosure :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    ∃ (B : X.QcAlgebraUnder) (i : B ⟶ A),
      Mono ((forget X).map i).right ∧
      ∀ (U : affineEtaleSite X) (a : sectionRing A U.obj),
        (∃ b : sectionRing B U.obj,
          ((InducedCategory.Hom.hom (((forget X).map i).right)).app (op U.obj)).hom b = a) ↔
        _root_.IsIntegral Γ(U.obj.left.left, ⊤) a)
