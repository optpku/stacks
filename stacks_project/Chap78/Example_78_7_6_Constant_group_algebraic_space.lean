/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup.Points

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ConstantGroup
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/- Example 78.7.6 (Constant group algebraic space) -/
@[stacks 043O] #check (AlgebraicGeometry.ConstantGroup.space :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}),
    GroupAlgebraicSpace B)
#check (AlgebraicGeometry.ConstantGroup.space_left :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}),
    (AlgebraicGeometry.ConstantGroup.space B G).X.left =
      CategoryTheory.Limits.pullback
        (toBase (AlgebraicGeometry.AlgebraicSpace.ofOver
          (AlgebraicGeometry.ConstantGroup.baseChange S G).X)) (toBase B))
#check (AlgebraicGeometry.ConstantGroup.homMulEquiv :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B),
    (Over.mk t ⟶ (AlgebraicGeometry.ConstantGroup.space B G).X) ≃*
      LocallyConstant T.left G)
#check (AlgebraicGeometry.ConstantGroup.homMulEquiv_naturality :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T T' : Over S) (baseMap : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B)
    (baseMap' : AlgebraicGeometry.AlgebraicSpace.ofOver T' ⟶ B)
    (testMap : T' ⟶ T) (h_over : ofOverMap testMap ≫ baseMap = baseMap')
    (point : Over.mk baseMap ⟶ (AlgebraicGeometry.ConstantGroup.space B G).X),
    AlgebraicGeometry.ConstantGroup.homMulEquiv G T' baseMap'
        (Over.homMk (V := Over.mk baseMap) (ofOverMap testMap) h_over ≫ point) =
      AlgebraicGeometry.ConstantGroup.pointsMap G testMap
        (AlgebraicGeometry.ConstantGroup.homMulEquiv G T baseMap point))
