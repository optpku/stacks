/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Twist

/-!
# Iterated relative Frobenius: basic maps

This leaf owns the `n`-fold relative Frobenius as a morphism in `Over S`, its
projection computations, and the successive relative-Frobenius step between
power twists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The pullback lift defining the iterated relative Frobenius is a morphism
over the original base scheme. -/
theorem iteratedRelativeFrobenius_lift_over (n : ℕ) :
    pullback.lift (Hom.absoluteFrobeniusPowSource (p := p) f n) f
        (Hom.absoluteFrobeniusPow_comm (p := p) f n) ≫
      (pPowerTwist (p := p) f n).hom = f := sorry

/-- The iterated relative Frobenius from `X/S` to its `p^n`-power twist,
defined for every natural number `n`. -/
def iteratedRelativeFrobenius (n : ℕ) :
    Over.mk f ⟶ pPowerTwist (p := p) f n :=
  Over.homMk
    (pullback.lift (Hom.absoluteFrobeniusPowSource (p := p) f n) f
      (Hom.absoluteFrobeniusPow_comm (p := p) f n))
    (iteratedRelativeFrobenius_lift_over (p := p) f n)

/-- The first projection of the iterated relative Frobenius is the iterated
absolute Frobenius of the source. -/
theorem iteratedRelativeFrobenius_fst (n : ℕ) :
    (iteratedRelativeFrobenius (p := p) f n).left ≫
        pullback.fst f (absoluteFrobeniusPow p S n) =
      Hom.absoluteFrobeniusPowSource (p := p) f n := sorry

/-- The iterated relative Frobenius is a morphism over `S`. -/
theorem iteratedRelativeFrobenius_over (n : ℕ) :
    (iteratedRelativeFrobenius (p := p) f n).left ≫
      (pPowerTwist (p := p) f n).hom = f := sorry

/-- The underlying scheme morphism of the relative Frobenius of the `n`-th
power twist, with target identified with the direct successor twist. -/
def successiveRelativeFrobeniusStepLeft (n : ℕ) :
    (pPowerTwist (p := p) f n).left ⟶
      (pPowerTwist (p := p) f (n + 1)).left :=
  Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom ≫
    (pullback.congrHom rfl (absoluteFrobenius_eq_absoluteFrobeniusPow_one p S)).hom ≫
    (pPowerTwistSuccIso (p := p) (f := f) n).hom.left

/-- The successive relative-Frobenius step is a morphism over the original
base scheme. -/
theorem successiveRelativeFrobeniusStep_over (n : ℕ) :
    successiveRelativeFrobeniusStepLeft (p := p) f n ≫
        (pPowerTwist (p := p) f (n + 1)).hom =
      (pPowerTwist (p := p) f n).hom := sorry

/-- The relative Frobenius of the `n`-th power twist, regarded over `S` with
target the direct successor twist. -/
@[stacks 0CCG]
def successiveRelativeFrobeniusStep (n : ℕ) :
    pPowerTwist (p := p) f n ⟶ pPowerTwist (p := p) f (n + 1) :=
  Over.homMk (successiveRelativeFrobeniusStepLeft (p := p) f n)
    (successiveRelativeFrobeniusStep_over (p := p) f n)

/-- The Frobenius-power twist of the relative-Frobenius target is canonically
isomorphic to the direct successor Frobenius-power twist. -/
def pPowerTwistRelativeFrobeniusTargetIso (n : ℕ) :
    (frobeniusPowerTwistFunctor p S n).obj
        (Hom.relativeFrobeniusTargetOver (p := p) f) ≅
      pPowerTwist (p := p) f (n + 1) :=
  (Over.pullbackComp (absoluteFrobeniusPow p S n) (absoluteFrobenius p S)).symm.app
    (Over.mk f)

/-- The `p^n`-power twist of the relative Frobenius, with its target identified
with the direct `(n + 1)`-st Frobenius-power twist. -/
def pPowerTwistRelativeFrobenius (n : ℕ) :
    pPowerTwist (p := p) f n ⟶ pPowerTwist (p := p) f (n + 1) :=
  (frobeniusPowerTwistFunctor p S n).map
      (Hom.relativeFrobeniusOver (p := p) f) ≫
    (pPowerTwistRelativeFrobeniusTargetIso (p := p) f n).hom

/-- The relative Frobenius of a Frobenius-power twist agrees with the
corresponding Frobenius-power twist of the original relative Frobenius. -/
theorem successiveRelativeFrobeniusStep_eq_pPowerTwistRelativeFrobenius (n : ℕ) :
    successiveRelativeFrobeniusStep (p := p) f n =
      pPowerTwistRelativeFrobenius (p := p) f n := sorry

/-- The direct iterated relative Frobenius at `n + 2` is obtained by composing
the one at `n + 1` with the successive relative-Frobenius step. -/
theorem iteratedRelativeFrobenius_succ (n : ℕ) :
    iteratedRelativeFrobenius (p := p) f (n + 1) ≫
        successiveRelativeFrobeniusStep (p := p) f (n + 1) =
      iteratedRelativeFrobenius (p := p) f (n + 2) := sorry

end AlgebraicGeometry.Scheme
