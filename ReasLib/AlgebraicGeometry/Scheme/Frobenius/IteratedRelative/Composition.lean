/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic

/-!
# Iterated relative Frobenius: composition formulas

This leaf records the two natural compositions of successive relative
Frobenii and compares them with the direct iterated relative Frobenius.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- For `n ≥ 1`, the composite of the relative Frobenii of `X/S`, its first
power twist, and the later successive power twists. -/
def successiveRelativeFrobeniusComposite :
    (n : ℕ) → 1 ≤ n → (Over.mk f ⟶ pPowerTwist (p := p) f n)
  | 0, hn => False.elim (Nat.not_succ_le_zero 0 hn)
  | 1, _ => iteratedRelativeFrobenius (p := p) f 1
  | n + 2, _ =>
      successiveRelativeFrobeniusComposite (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) ≫
        successiveRelativeFrobeniusStep (p := p) f (n + 1)

/-- The composite of successive relative Frobenii at a successor index, with
the positivity witness supplied canonically. -/
abbrev successiveRelativeFrobeniusCompositeSucc (n : ℕ) :
    Over.mk f ⟶ pPowerTwist (p := p) f (n + 1) :=
  successiveRelativeFrobeniusComposite (p := p) f (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))

/-- The iterated relative Frobenius is the composite of the successive
relative Frobenii of the Frobenius-power twists. -/
@[stacks 0CCG]
theorem iteratedRelativeFrobenius_eq_successiveRelativeFrobeniusComposite
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedRelativeFrobenius (p := p) f n =
      successiveRelativeFrobeniusComposite (p := p) f n hn := sorry

/-- For `n ≥ 1`, the composite of the successive Frobenius-power twists of
the original relative Frobenius. -/
def pPowerTwistRelativeFrobeniusComposite :
    (n : ℕ) → 1 ≤ n → (Over.mk f ⟶ pPowerTwist (p := p) f n)
  | 0, hn => False.elim (Nat.not_succ_le_zero 0 hn)
  | 1, _ => iteratedRelativeFrobenius (p := p) f 1
  | n + 2, _ =>
      pPowerTwistRelativeFrobeniusComposite (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) ≫
        pPowerTwistRelativeFrobenius (p := p) f (n + 1)

/-- The iterated relative Frobenius is the composite of the Frobenius-power
twists of the original relative Frobenius. -/
theorem iteratedRelativeFrobenius_eq_pPowerTwistComposite
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedRelativeFrobenius (p := p) f n =
      pPowerTwistRelativeFrobeniusComposite (p := p) f n hn := sorry

end AlgebraicGeometry.Scheme
