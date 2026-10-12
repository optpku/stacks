/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup.Points

/-! Compatibility checks for points of the constant group algebraic space. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ConstantGroup

universe u

#check (AlgebraicGeometry.ConstantGroup.homMulEquiv :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B),
    (Over.mk t ⟶ (AlgebraicGeometry.ConstantGroup.space B G).X) ≃*
      LocallyConstant T.left G)
#check (AlgebraicGeometry.ConstantGroup.pointsFibreEquiv :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B),
    AlgebraicGeometry.ConstantGroup.pointsFibre G T t ≃ LocallyConstant T.left G)
