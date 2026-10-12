/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.5: affine schemes are equivalent to the opposite category of
commutative rings through global sections. -/
@[stacks 01I2] #check AffineScheme.equivCommRingCat
#check AffineScheme.Γ
