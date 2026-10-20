/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.ConstantGroup

/-!
# Constant group algebraic spaces

The constant group algebraic space over an algebraic space `B` over a scheme `S` is the
base change of the constant group scheme over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
open CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ConstantGroup

/-- The constant group scheme `G_S` viewed as a group object in the slice over `S`. -/
noncomputable instance instGrpObjOfOver (S : Scheme.{u}) (G : GrpCat.{u}) :
    GrpObj (Over.mk (toBase (ofOver (baseChange S G).X))) where
  one := Over.homMk (ofOverMap (η[(baseChange S G).X])) sorry
  mul :=
    Over.homMk
      (ofOverPullbackHom (baseChange S G).X (baseChange S G).X ≫
        tensorComparison (baseChange S G).X (baseChange S G).X ≫
        ofOverMap (μ[(baseChange S G).X]))
      sorry
  inv := Over.homMk (ofOverMap (ι[(baseChange S G).X])) sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The constant group algebraic space `G_B = B ×_S G_S` over an algebraic space `B`. -/
def space {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}) :
    GroupAlgebraicSpace B :=
  (Over.pullback (toBase B)).mapGrp.obj
    (.mk (Over.mk (toBase (ofOver (baseChange S G).X))))

/-- The underlying object of `space B G` is the pullback of `G_S` along `toBase B`. -/
theorem space_X {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}) :
    (space B G).X =
      (Over.pullback (toBase B)).obj (Over.mk (toBase (ofOver (baseChange S G).X))) :=
  sorry

/-- The underlying algebraic space of `space B G` is the fibre product of the structure maps. -/
theorem space_left {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}) :
    (space B G).X.left =
      Limits.pullback (toBase (ofOver (baseChange S G).X)) (toBase B) :=
  sorry

end AlgebraicGeometry.ConstantGroup
