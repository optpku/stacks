/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_11_9_DualNumber
public import stacks_project.Chap90.Definition_90_11_9_TangentSpace
import StacksCheckRecall

/-!
# Tangent space of a functor

The tangent space `TF` of a set-valued functor `F` on a category as in
Lemma 90.11.8, with `F(R)` a singleton, is `F(R[ε])`.
-/

@[expose] public section

open CategoryTheory
open TrivSqZeroExt
open scoped DualNumber

universe u

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
variable (F : P.FullSubcategory ⥤ Type u)

/- Definition 90.11.9: Let `C` be a category as in Lemma 90.11.8. Let
`F : C ⥤ Type` be a functor such that `F(R)` is a one-element set. The tangent
space `TF` of `F` is `F(R[ε])`. -/
@[stacks 06IB]
#check TrivSqZeroExt.tangentSpace

/-- The tangent space `TF` of `F` is `F(R[ε])`. -/
@[stacks 06IB]
theorem TrivSqZeroExt.tangentSpace_eq [Unique (F.obj (overSelfObj P))] :
    tangentSpace F = F.obj (dualNumberObj P) := sorry
