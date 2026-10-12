/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import stacks_project.Chap99.Lemma_99_13_1
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Lemma 99.13.2

The diagonal of `Spaces'_{fp, flat, proper}` is representable by algebraic
spaces.
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

/-- `isomOverLeft x y` is precomposition of
`Functor.isomorphismPresheaf (pFpFlatProperGroupoids S) x y` with the opposite
of the iterated-slice inverse. -/
theorem isomOverLeft_eq {S : Scheme.{u}} {U : Over S}
    (x y : (pFpFlatProperGroupoids S).Fiber U) :
    isomOverLeft x y =
      U.iteratedSliceEquiv.inverse.op ⋙
        Functor.isomorphismPresheaf (pFpFlatProperGroupoids S) x y :=
  sorry

/-- Every pair of fibre objects of `pFpFlatProperGroupoids S` has an
algebraic-space isomorphism presheaf over its base, after universe lift of the
functor of points. This is the Isom criterion of Algebraic Stacks,
Lemma 94.10.11 used in the source proof. -/
theorem isom_isAlgebraicSpace (S : Scheme.{u}) {U : Over S}
    (x y : (pFpFlatProperGroupoids S).Fiber U) :
    ∃ F : AlgebraicSpace U.left,
      Nonempty
        (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- Lemma 99.13.2: the diagonal
`Δ : Spaces'_{fp, flat, proper} ⟶ Spaces'_{fp, flat, proper} × Spaces'_{fp, flat, proper}`
is representable by algebraic spaces. -/
@[stacks 0D1F]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal (S : Scheme.{u}) :
    Classifying.relativelyRepresentableByAlgebraicSpaces
      (CohStack.diagonal (toGroupoids S)) :=
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
