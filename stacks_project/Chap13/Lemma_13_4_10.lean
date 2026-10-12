/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Biproduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.10

The reusable owner is CategoryTheory.Pretriangulated.biproductTriangle.
Mathlib's binaryBiproductTriangle is a different split triangle on two
objects; this item concerns the objectwise biproduct of arbitrary triangles.
-/

/- Lemma 13.4.10 (Stacks 05QS): an objectwise binary biproduct triangle is
distinguished if and only if its two summands are distinguished. -/
@[stacks 05QS] #check @CategoryTheory.Pretriangulated.biproductTriangle.distinguished_iff

#check @CategoryTheory.Pretriangulated.biproductTriangle
#check @CategoryTheory.Pretriangulated.biproductTriangle.inl
#check @CategoryTheory.Pretriangulated.biproductTriangle.fst
#check @CategoryTheory.Pretriangulated.biproductTriangle.lift
#check @CategoryTheory.Pretriangulated.biproductTriangle.desc
#check @CategoryTheory.Pretriangulated.biproductTriangle.bicone
#check @CategoryTheory.Pretriangulated.biproductTriangle.isBilimit
