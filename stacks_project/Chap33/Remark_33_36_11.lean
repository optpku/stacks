/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative

@[expose] public section

/-!
# Remark 33.36.11 compatibility entry point

The iterated absolute Frobenius, Frobenius-power twists, iterated relative
Frobenius maps, their composition formulas, and their naturality API are owned
by `ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Remark 33.36.11: the iterated relative Frobenius is the composite of the
Frobenius-power twists of the original relative Frobenius. -/
@[stacks 0CCG] #check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius_eq_pPowerTwistComposite :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ) (hn : 1 ≤ n),
      Scheme.iteratedRelativeFrobenius (p := p) f n =
        Scheme.pPowerTwistRelativeFrobeniusComposite (p := p) f n hn)

#check
  (AlgebraicGeometry.Scheme.frobeniusPowerTwistFunctor :
    ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [Scheme.IsCharP S p] (n : ℕ),
      Over S ⥤ Over S)

#check
  (AlgebraicGeometry.Scheme.pPowerTwist :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ), Over S)

#check
  (AlgebraicGeometry.Scheme.pPowerTwist_isPullback :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ),
      IsPullback (pullback.fst f (Scheme.absoluteFrobeniusPow p S n))
        (Scheme.pPowerTwist (p := p) f n).hom f
        (Scheme.absoluteFrobeniusPow p S n))

#check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ),
      Over.mk f ⟶ Scheme.pPowerTwist (p := p) f n)

#check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius_fst :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ),
      (Scheme.iteratedRelativeFrobenius (p := p) f n).left ≫
          pullback.fst f (Scheme.absoluteFrobeniusPow p S n) =
        Scheme.Hom.absoluteFrobeniusPowSource (p := p) f n)

#check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius_over :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ),
      (Scheme.iteratedRelativeFrobenius (p := p) f n).left ≫
          (Scheme.pPowerTwist (p := p) f n).hom = f)

#check
  (AlgebraicGeometry.Scheme.successiveRelativeFrobeniusStep_eq_pPowerTwistRelativeFrobenius :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ),
      Scheme.successiveRelativeFrobeniusStep (p := p) f n =
        Scheme.pPowerTwistRelativeFrobenius (p := p) f n)

#check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius_eq_successiveRelativeFrobeniusComposite :
    ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
      [Scheme.IsCharP S p] (n : ℕ) (hn : 1 ≤ n),
      Scheme.iteratedRelativeFrobenius (p := p) f n =
        Scheme.successiveRelativeFrobeniusComposite (p := p) f n hn)

#check
  (AlgebraicGeometry.Scheme.iteratedRelativeFrobenius_commSq :
    ∀ {p : ℕ} [Fact p.Prime] {X Y S : Scheme.{u}}
      (x : X ⟶ S) (y : Y ⟶ S) (f : X ⟶ Y) [Scheme.IsCharP S p]
      (n : ℕ) (h_over : f ≫ y = x),
      CommSq (Scheme.iteratedRelativeFrobenius (p := p) x n).left f
        (Scheme.pPowerTwistMap (p := p) x y f n h_over)
        (Scheme.iteratedRelativeFrobenius (p := p) y n).left)
