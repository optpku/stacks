module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.TangentSpace
import StacksCheckRecall

/-!
# Tangent space of a functor

The tangent space `TF` of a set-valued functor `F` on a category as in
Lemma 90.11.8, with `F(R)` a singleton, is `F(R[ε])`.
-/

open CategoryTheory

universe u

/- Definition 90.11.9: Let `C` be a category as in Lemma 90.11.8. Let
`F : C ⥤ Type` be a functor such that `F(R)` is a one-element set. The tangent
space `TF` of `F` is `F(R[ε])`. -/
@[stacks 06IB]
#check (TrivSqZeroExt.tangentSpace :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    [Unique (F.obj (TrivSqZeroExt.overSelfObj P))], Type u)
