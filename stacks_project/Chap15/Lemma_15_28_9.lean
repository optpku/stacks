/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Homotopy.CofiberScalarMul
import StacksCheckRecall

/-!
# Homotopy cofiber of a product scalar

The reusable chain-complex statement is owned by `ReasLib`.  This chapter file records the
source label directly and does not rebuild the connecting map through degreewise cone
coordinates.

@stack 062A
-/

@[expose] public section

/- Lemma 15.28.9: the cone of multiplication by `f * g` is homotopy equivalent to the cone of a
map from the shifted `f`-cone to the `g`-cone. -/
@[stacks 062A]
#check @ChainComplex.homotopyCofiber.exists_homotopyEquiv_smul_mul
