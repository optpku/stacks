module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Pullback
import StacksCheckRecall

/-!
# Lemma 71.17.9

The pullback of every effective Cartier divisor along a blowup morphism of
algebraic spaces is defined.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.17.9: For a blowup of an algebraic space over a scheme in a closed
subspace, the pullback of every effective Cartier divisor is defined. -/
@[stacks 085X] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.pullbackDefined :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι], D.IsPullbackDefined π.hom)
