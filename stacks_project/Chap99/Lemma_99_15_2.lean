/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Lemma 99.15.2

The category Curves of families of curves is fibred in groupoids over
`Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 99.15.2: the category Curves of families of curves is fibred in
groupoids over `Sch_fppf`, via the forgetful functor `p S : Obj S ⥤ Over S`,
with `Over S` playing the role of `Sch_fppf`. -/
@[stacks 0D51]
instance instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (p S) := sorry

/-- The category of families of curves, bundled as a category fibred in
groupoids over `Over S`. The Hom-universe is `u + 1` because
`Category (AlgebraicSpace S)` is `Category.{u + 1}`, so this cannot land in
`GroupoidsOver S`, which pins Hom-universe `u`. -/
def toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p S)

/-- The projection of `toGroupoids S` is the forgetful functor `p S`. -/
theorem toGroupoids_p (S : Scheme.{u}) : (toGroupoids S).p = p S := sorry

/-- The total category of `toGroupoids S` is the category `Obj S` of
Situation 99.15.1. -/
theorem toGroupoids_total (S : Scheme.{u}) : (toGroupoids S).total = Obj S :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces

