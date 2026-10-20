module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 31.18.1

Base change of relative effective Cartier divisors.

@stack 056Q
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.18.1: An effective Cartier divisor flat over the base remains effective Cartier after
arbitrary base change. -/
@[stacks 056Q] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.isEffectiveCartierDivisor_comap_pullback_fst :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      (D : X.IdealSheafData) [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D],
      AlgebraicGeometry.IsEffectiveCartierDivisor
        (D.comap (CategoryTheory.Limits.pullback.fst f g)).subschemeι)

#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.comap_pullback_fst :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      (D : X.IdealSheafData) [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D],
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor
        (CategoryTheory.Limits.pullback.snd f g)
        (D.comap (CategoryTheory.Limits.pullback.fst f g)))
