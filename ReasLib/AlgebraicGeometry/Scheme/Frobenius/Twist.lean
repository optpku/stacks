/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Iteration

/-!
# Frobenius power twists

This leaf owns base change along iterates of absolute Frobenius, both as a
functor on a slice category and as an object attached to a scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Base change on `Over S` along the `n`-fold absolute Frobenius of `S`. -/
abbrev frobeniusPowerTwistFunctor (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] (n : ℕ) : Over S ⥤ Over S :=
  Over.pullback (absoluteFrobeniusPow p S n)

/-- The structure morphism of the Frobenius-power twist of an object of
`Over S` is the second pullback projection. -/
theorem frobeniusPowerTwistFunctor_obj_hom (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] (n : ℕ) (X : Over S) :
    ((frobeniusPowerTwistFunctor p S n).obj X).hom =
      pullback.snd X.hom (absoluteFrobeniusPow p S n) := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The `p^n`-power Frobenius twist of a scheme morphism `f : X ⟶ S`. -/
abbrev pPowerTwist (n : ℕ) : Over S :=
  Over.mk (pullback.snd f (Scheme.absoluteFrobeniusPow p S n))

/-- The `p^n`-power Frobenius twist is the pullback square of `f` along the
`n`-fold absolute Frobenius of `S`. -/
theorem pPowerTwist_isPullback (n : ℕ) :
    IsPullback (pullback.fst f (Scheme.absoluteFrobeniusPow p S n))
      (pPowerTwist (p := p) f n).hom f (Scheme.absoluteFrobeniusPow p S n) := sorry

/-- Every Frobenius-power twist over a characteristic-`p` base is canonically
a scheme of characteristic `p`. -/
instance pPowerTwist_isCharP (n : ℕ) :
    Scheme.IsCharP (pPowerTwist (p := p) f n).left p :=
  Hom.isCharP_of_target (pPowerTwist (p := p) f n).hom

/-- The one-step twist of the `n`-th Frobenius-power twist, still regarded as
an object over the original base `S`. -/
abbrev pPowerTwistStep (n : ℕ) : Over S :=
  let f' : (pPowerTwist (p := p) f n).left ⟶ S :=
    (pPowerTwist (p := p) f n).hom
  Over.mk (pullback.snd f' (Scheme.absoluteFrobeniusPow p S 1))

/-- The standard pullback comparison between a successive Frobenius-power
twist and the direct `(n + 1)`-st twist is a morphism over `S`. -/
theorem pPowerTwistSuccIso_hom_over (n : ℕ) :
    ((pullbackLeftPullbackSndIso f (Scheme.absoluteFrobeniusPow p S n)
          (Scheme.absoluteFrobenius p S)) ≪≫
        pullback.congrHom rfl (Scheme.absoluteFrobeniusPow_left_comm p S n)).hom ≫
          pullback.snd f (Scheme.absoluteFrobeniusPow p S (n + 1)) =
      pullback.snd (pullback.snd f (Scheme.absoluteFrobeniusPow p S n))
        (Scheme.absoluteFrobeniusPow p S 1) := sorry

/-- The one-step twist of the `n`-th Frobenius-power twist is canonically
isomorphic over `S` to the direct `(n + 1)`-st twist. -/
def pPowerTwistSuccIso (n : ℕ) :
    pPowerTwistStep (p := p) (f := f) n ≅ pPowerTwist (p := p) f (n + 1) :=
  Over.isoMk
    ((pullbackLeftPullbackSndIso f (Scheme.absoluteFrobeniusPow p S n)
        (Scheme.absoluteFrobenius p S)) ≪≫
      pullback.congrHom rfl (Scheme.absoluteFrobeniusPow_left_comm p S n))
    (pPowerTwistSuccIso_hom_over (p := p) f n)

end AlgebraicGeometry.Scheme
