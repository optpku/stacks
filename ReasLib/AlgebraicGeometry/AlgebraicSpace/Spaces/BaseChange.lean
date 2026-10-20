module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CostructuredArrow
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize.Basic

/-!
# Base-change pair categories of primed algebraic spaces

Finite-type families whose base scheme maps to an algebraic space form a
costructured-arrow category. Its two projections give a categorical pullback
square. The same construction applies to finite-presentation, flat, proper families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The category of finite-type primed families equipped with a morphism from
 their base scheme to B; morphisms commute with these structural morphisms. -/
abbrev FtGroupoidsOver {S : Scheme.{u}} (B : AlgebraicSpace S) : Type (u + 1) :=
  CostructuredArrow (pFtGroupoids S ⋙ ofOverFunctor S) B

namespace FtGroupoidsOver

/-- The projection square forgetting the morphism to B horizontally and
 remembering the base scheme with its morphism to B vertically. -/
abbrev square {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver (pFtGroupoids S) (CostructuredArrow.proj (ofOverFunctor S) B)
      (FtGroupoidsOver B) :=
  CategoricalPullback.CostructuredArrow.square (pFtGroupoids S) (ofOverFunctor S) B

/-- Finite-type primed families with a morphism from their base scheme to B
 form the 2-fibre product of the family category and schemes over B over schemes over S. -/
@[stacks 0D1H, instance]
instance instSquareIsBilimit {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver.Resized.IsBilimit (square B) :=
  sorry

end FtGroupoidsOver

/-- The category of finite-presentation, flat, proper primed families equipped
 with a morphism from their base scheme to B; morphisms commute with these maps. -/
abbrev FpFlatProperGroupoidsOver {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Type (u + 1) :=
  CostructuredArrow (pFpFlatProperGroupoids S ⋙ ofOverFunctor S) B

namespace FpFlatProperGroupoidsOver

/-- The projection square forgetting the morphism to B horizontally and
 remembering the base scheme of a finite-presentation, flat, proper family vertically. -/
abbrev square {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver (pFpFlatProperGroupoids S)
      (CostructuredArrow.proj (ofOverFunctor S) B) (FpFlatProperGroupoidsOver B) :=
  CategoricalPullback.CostructuredArrow.square
    (pFpFlatProperGroupoids S) (ofOverFunctor S) B

/-- Finite-presentation, flat, proper primed families with a morphism from their
 base scheme to B form the 2-fibre product with schemes over B over schemes over S. -/
@[stacks 0D1H, instance]
instance instSquareIsBilimit {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver.Resized.IsBilimit (square B) :=
  sorry

end FpFlatProperGroupoidsOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
