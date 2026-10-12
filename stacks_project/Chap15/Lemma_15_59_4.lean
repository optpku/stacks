/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Tensor
import StacksCheckRecall

/-!
# Lemma 15.59.4

@stack 0795

Tensor closure is owned at the coefficient-category level by
`CochainComplex.IsKFlat.tensor`.  This avoids a chapter-local associator and
lets module, sheaf, and derived-category consumers share the same theorem.  The recall below is
the current `ModuleCat` specialization for a commutative ring; the reusable owner itself is
formulated for an arbitrary suitable monoidal preadditive category.
-/

@[expose] public section

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]

/- Lemma 15.59.4 (0795): the totalized tensor product of two K-flat
cochain complexes is K-flat. -/
@[stacks 0795 "K-flat complexes are closed under tensor products"]
#check @CochainComplex.IsKFlat.tensor (ModuleCat R)
