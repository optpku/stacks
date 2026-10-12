/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import stacks_project.Chap101.Remark_101_5_2_Group
public import stacks_project.Chap101.Remark_101_5_2_SpacesOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia as a group object

For a morphism of algebraic stacks, the inertia stack of `X / Y` is a group
object in the 1-category of morphisms `Z ⟶ X` representable by algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.SpacesOver
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

/-- Remark 101.5.2: Let `f : X ⟶ Y` be a morphism of algebraic stacks. In the
1-category of morphisms `Z ⟶ X` representable by algebraic spaces, obtained as
the homotopy category of `SpacesOver X`, the relative inertia stack
`I_{X/Y}` is a group object. An object of `I_{X/Y}` is a pair `(x, α)` with
`x` an object of `X` and `α` an automorphism of `x` in its fibre category
satisfying `f(α) = id`. Multiplication
`I_{X/Y} ×_X I_{X/Y} ⟶ I_{X/Y}` is given on objects by
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`, and the unit
`X ⟶ I_{X/Y}` is `x ↦ (x, id_x)`. -/
@[stacks 050R, instance]
instance instGrpObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    GrpObj (asHomotopy f) where
  one := Bicategory.HomotopyCategory.mkHom (oneHom f)
  mul := Bicategory.HomotopyCategory.mkHom (mulHom f)
  inv := Bicategory.HomotopyCategory.mkHom (invHom f)
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
