/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap99.«99_15_1_1_Curves»
public import stacks_project.Chap99.Lemma_99_13_1
public import stacks_project.Chap99.Lemma_99_15_2

/-!
# The Curves inclusion as a 1-morphism of groupoid fibrations

Equation (99.15.1.1) is the full-subcategory inclusion of families of curves
into `Spaces'_{fp, flat, proper}`. This module packages that functor as a
1-morphism of categories fibred in groupoids over `Over S`, at Hom-universe
`u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace CurvesGroupoids

/-- The 1-morphism (99.15.1.1) `Curves ⟶ Spaces'_{fp, flat, proper}`, packaged
as a morphism of categories fibred in groupoids over `Over S`. The underlying
functor is the full-subcategory inclusion of families of curves; this is the
same inclusion as `CurvesGroupoids.inclusion` after identifying `curves S` with
`Curves.relativeDimensionLE S 1`. -/
def inclusionHom (S : Scheme.{u}) :
    Curves.toGroupoids S ⟶ FpFlatProperGroupoids.toGroupoids S :=
  Groupoids.ofBasedFunctor
    { toFunctor := Curves.inclusion S
      w := sorry }

/-- The underlying functor of `inclusionHom` is the full-subcategory inclusion
of families of curves. -/
theorem inclusionHom_toFunctor (S : Scheme.{u}) :
    Groupoids.toFunctor (inclusionHom S) = Curves.inclusion S := sorry

/-- `inclusionHom` lies strictly over `Over S`. -/
theorem inclusionHom_comm (S : Scheme.{u}) :
    Groupoids.toFunctor (inclusionHom S) ⋙ pFpFlatProperGroupoids S =
      Curves.p S := sorry

end CurvesGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
