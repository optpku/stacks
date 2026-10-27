/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

/-!
# Diagonal of finitely presented, flat, proper algebraic spaces

The fibrewise isomorphism presheaves and the canonical diagonal of the category
of finitely presented, flat, proper algebraic spaces are representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupScheme
open Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

/-- The isomorphism presheaf `Isom(x, y)` of two fibre objects of
`pFpFlatProperGroupoids S` over a scheme `U` over `S`, reindexed along
`U.iteratedSliceEquiv` to a presheaf on schemes over `U.left`. Hom-types of
`FpFlatProperGroupoids S` live in `Type (u + 1)`. -/
def isomOverLeft {S : Scheme.{u}} {U : Over S}
    (x y : (pFpFlatProperGroupoids S).Fiber U) :
    (Over U.left)ᵒᵖ ⥤ Type (u + 1) :=
  U.iteratedSliceEquiv.inverse.op ⋙
    Functor.isomorphismPresheaf (pFpFlatProperGroupoids S) x y

/-- The isomorphism presheaf of two finitely presented, flat, proper algebraic
spaces in the same fibre is represented by an algebraic space over their base,
after universe lift of its functor of points. -/
theorem isom_isAlgebraicSpace (S : Scheme.{u}) {U : Over S}
    (x y : (pFpFlatProperGroupoids S).Fiber U) :
    ∃ F : AlgebraicSpace U.left,
      Nonempty
        (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) := sorry

/-- The canonical diagonal of the category fibred in groupoids of finitely
presented, flat, proper algebraic spaces is representable by algebraic spaces. -/
@[stacks 0D1F]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal (S : Scheme.{u}) :
    Classifying.relativelyRepresentableByAlgebraicSpaces
      (CohStack.diagonal (toGroupoids S)) := sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
