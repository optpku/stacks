module

public import stacks_project.Chap71.Lemma_71_9_1_BaseChange
import StacksCheckRecall

/-!
# Lemma 71.9.1

Base change of relative effective Cartier divisors on algebraic spaces.

@stack 0EPN
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 71.9.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `D ⊂ X` be a closed subspace. Assume `D` is an effective
Cartier divisor, and `D ⟶ Y` is a flat morphism. Then for every morphism of
schemes `g : Y' ⟶ Y` the inverse image `(g')⁻¹D` along the projection
`g' : X' ⟶ X` of `X' = Y' ×_Y X` is an effective Cartier divisor on `X'`. -/
@[stacks 0EPN] #check
  (IsRelativeEffectiveCartierDivisor.isEffectiveCartierDivisor_inverseImage_pullback_fst :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : ClosedSubspace X)
      [IsRelativeEffectiveCartierDivisor f D.ι] {Y' : Over S} (g : ofOver Y' ⟶ Y),
      IsEffectiveCartierDivisor (D.inverseImage (pullback.fst f g)).ι)

#check
  (IsRelativeEffectiveCartierDivisor.inverseImage_pullback_fst :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : ClosedSubspace X)
      [IsRelativeEffectiveCartierDivisor f D.ι] {Y' : Over S} (g : ofOver Y' ⟶ Y),
      IsRelativeEffectiveCartierDivisor (pullback.snd f g)
        (D.inverseImage (pullback.fst f g)).ι)
