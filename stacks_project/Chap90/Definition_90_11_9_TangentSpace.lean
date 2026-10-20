module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.TangentSpace

/-!
# Tangent space of a set-valued functor

The tangent space `TF` of a functor `F` on a strictly full subcategory of
`S`-Alg/`R` containing every `R[M]`, with `F(R)` a singleton, is the value
`F(R[ε])`.
-/

open CategoryTheory

universe u

#check (TrivSqZeroExt.tangentSpace :
  ∀ {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    [Unique (F.obj (TrivSqZeroExt.overSelfObj P))], Type u)
