/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Picard
import StacksCheckRecall

/-!
# Equation 31.27.5.1

The canonical comparison homomorphism from the Picard group to the Weil divisor class group.

@stack 0BE7
-/

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/- 31.27.5.1: the canonical comparison homomorphism `Pic(X) ⟶ Cl(X)`. -/
@[stacks 0BE7] #check
  (AlgebraicGeometry.Scheme.picardToWeilDivisorClassGroup X :
    X.PicardGroup →+ AlgebraicGeometry.WeilDivisorClassGroup X)
