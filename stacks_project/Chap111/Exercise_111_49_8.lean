module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Difference
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.49.8 -/
@[stacks 02FB] #check (AlgebraicGeometry.exists_cartierDivisor_not_sub_ofEffectiveCartier :
    ∃ (k : Type u) (_ : Field k) (X : AlgebraicGeometry.SchemeOverField k)
      (_ : AlgebraicGeometry.Variety X)
      (τ : AlgebraicGeometry.Scheme.CartierDivisor X.left),
      ¬ AlgebraicGeometry.Scheme.IsDifferenceOfEffectiveCartier τ)
