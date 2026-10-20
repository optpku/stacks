module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral
import StacksCheckRecall

/-!
# Integral morphisms of algebraic spaces versus affine universally closed morphisms

A morphism of algebraic spaces is integral if and only if it is affine and
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.45.7: A morphism of algebraic spaces over a scheme is integral if
and only if it is affine and universally closed. -/
@[stacks 0415] #check
  (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.IsIntegralHom f ↔
        AlgebraicGeometry.AlgebraicSpace.UniversallyClosed f ∧
          AlgebraicGeometry.AlgebraicSpace.Affine f)
