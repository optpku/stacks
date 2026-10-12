/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Remark_99_15_5_BaseChange

/-!
# The category `B`-Curves as a groupoid fibration

The pair category `B`-Curves of Remark 99.15.5 is packaged as a category fibred
in groupoids over `Over S`, at Hom-universe `u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace CurvesGroupoidsOver

/-- The forgetful functor `B`-Curves `⟶` `Sch_fppf`, sending a pair
`(P, h : ofOver (p.obj P) ⟶ B)` to the base scheme of `P`. Here `Over S` plays
the role of `Sch_fppf`. -/
def p {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CurvesGroupoidsOver B ⥤ Over S :=
  CostructuredArrow.proj (pCurvesGroupoids S ⋙ ofOverFunctor S) B ⋙
    pCurvesGroupoids S

/-- The projection `p B` is the costructured-arrow projection of
`pCurvesGroupoids S ⋙ ofOverFunctor S`, followed by `pCurvesGroupoids S`. -/
theorem p_eq {S : Scheme.{u}} (B : AlgebraicSpace S) :
    p B =
      CostructuredArrow.proj (pCurvesGroupoids S ⋙ ofOverFunctor S) B ⋙
        pCurvesGroupoids S :=
  sorry

/-- The forgetful functor of `B`-Curves is fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Functor.IsFibered.InGroupoids (p B) :=
  sorry

/-- The category `B`-Curves, bundled as a category fibred in groupoids over
`Over S`. The Hom-universe is `u + 1` because `Category (AlgebraicSpace S)` is
`Category.{u + 1}`, so this cannot land in `GroupoidsOver S`. -/
def toGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p B)

/-- The projection of `toGroupoids B` is the forgetful functor `p B`. -/
theorem toGroupoids_p {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (toGroupoids B).p = p B :=
  sorry

/-- The total category of `toGroupoids B` is the pair category
`CurvesGroupoidsOver B` of Remark 99.15.5. -/
theorem toGroupoids_total {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (toGroupoids B).total = CurvesGroupoidsOver B :=
  sorry

end CurvesGroupoidsOver
end AlgebraicGeometry.AlgebraicSpace.Spaces
