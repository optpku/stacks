module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Naturality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 33.36.5 source bridge

The naturality square for relative Frobenius is checked directly against its
shared mathematical owner.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

variable {p : ℕ} [Fact p.Prime]
variable {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (f : X ⟶ Y)
variable [Scheme.IsCharP S p] (h_over : f ≫ y = x)

/- Lemma 33.36.5: relative Frobenius is natural for morphisms of schemes over a
characteristic-`p` base. -/
@[stacks 0CCA] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_commSq (p := p) x y f h_over :
    CommSq
      (AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) x)
      f
      (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTargetMap (p := p) x y f h_over)
      (AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) y))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTargetMap (p := p) x y f h_over :
    pullback x (Scheme.absoluteFrobenius p S) ⟶
      pullback y (Scheme.absoluteFrobenius p S))
