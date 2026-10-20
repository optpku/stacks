module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic

/-!
# Naturality of iterated relative Frobenius

This leaf provides the maps induced between Frobenius power twists by a
morphism over the base and the resulting naturality square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (f : X ⟶ Y)
variable [Scheme.IsCharP S p]

/-- The map between `p^n`-power twists induced by a morphism in `Over S`. -/
def pPowerTwistOverMap (n : ℕ) (h_over : f ≫ y = x) :
    pPowerTwist (p := p) x n ⟶ pPowerTwist (p := p) y n :=
  (frobeniusPowerTwistFunctor p S n).map
    (Over.homMk (U := Over.mk x) (V := Over.mk y) f h_over)

/-- The map between the `p^n`-power twists induced by a scheme morphism over
the base. -/
def pPowerTwistMap (n : ℕ) (h_over : f ≫ y = x) :
    (pPowerTwist (p := p) x n).left ⟶ (pPowerTwist (p := p) y n).left :=
  (pPowerTwistOverMap (p := p) x y f n h_over).left

/-- The induced map between Frobenius power twists is a morphism over `S`. -/
theorem pPowerTwistMap_over (n : ℕ) (h_over : f ≫ y = x) :
    pPowerTwistMap (p := p) x y f n h_over ≫
        (pPowerTwist (p := p) y n).hom =
      (pPowerTwist (p := p) x n).hom := sorry

/-- The iterated relative Frobenius is natural for a morphism of schemes over
a characteristic-`p` base. -/
theorem iteratedRelativeFrobenius_commSq (n : ℕ) (h_over : f ≫ y = x) :
    CommSq
      (iteratedRelativeFrobenius (p := p) x n).left
      f
      (pPowerTwistMap (p := p) x y f n h_over)
      (iteratedRelativeFrobenius (p := p) y n).left := sorry

end AlgebraicGeometry.Scheme
