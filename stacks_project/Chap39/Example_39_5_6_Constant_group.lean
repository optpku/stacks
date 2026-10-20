/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ConstantGroup

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalCategory

universe u

/- Example 39.5.6 (Constant group) (1): the constant scheme on `G` is the
coproduct of copies of `Spec ℤ` indexed by `G`. -/
@[stacks 03YW] #check
  (AlgebraicGeometry.ConstantGroup.scheme_def :
    ∀ (G : GrpCat.{u}),
      AlgebraicGeometry.ConstantGroup.scheme G =
        ∐ fun _ : G ↦ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ)))

/- Example 39.5.6 (Constant group) (2): the group-valued functor of points of
the constant scheme is the functor of locally constant `G`-valued maps. -/
@[stacks 03YW] #check
  (AlgebraicGeometry.ConstantGroup.pointsIso :
    ∀ (G : GrpCat.{u}),
      CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.overSpecZ G) ≅
        AlgebraicGeometry.ConstantGroup.points
          (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))) G)

/- Example 39.5.6 (Constant group) (3): multiplication sends the component
indexed by `(g, g')` to the component indexed by `g * g'`. -/
@[stacks 03YW] #check
  (AlgebraicGeometry.ConstantGroup.mul_component :
    ∀ (G : GrpCat.{u}) (g g' : G),
      CartesianMonoidalCategory.lift
          (AlgebraicGeometry.ConstantGroup.component G g)
          (AlgebraicGeometry.ConstantGroup.component G g') ≫
        μ[(AlgebraicGeometry.ConstantGroup.overSpecZ G).X] =
          AlgebraicGeometry.ConstantGroup.component G (g * g'))

/- Example 39.5.6 (Constant group) (4): after base change to any scheme `S`,
the group-valued functor of points is still locally constant `G`-valued maps. -/
@[stacks 03YW] #check
  (AlgebraicGeometry.ConstantGroup.baseChangePointsIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (G : GrpCat.{u}),
      CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G) ≅
        AlgebraicGeometry.ConstantGroup.points S G)
