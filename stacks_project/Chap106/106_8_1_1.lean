module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
variable (i : T ⟶ T') [IsFirstOrderThickening i.left]
variable (f : X ⟶ Y) (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
variable (γ : overMap i ≫ y ≅ x ≫ f)
variable (x' : GroupoidsOver.slice T' ⟶ X)

/- 106.8.1.1: the solid 2-commutative square for a morphism `f : X ⟶ Y` of
algebraic stacks, with affine first-order thickening `i : T ⟶ T'`, points
`x : GroupoidsOver.slice T ⟶ X` and `y : GroupoidsOver.slice T' ⟶ Y`, and
witness `γ : overMap i ≫ y ≅ x ≫ f`. -/
@[stacks 0DNX] #check (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ : Bicategory.PseudoPullbackCone y f)

/- Companion check: the displayed dotted diagonal has type
`GroupoidsOver.slice T' ⟶ X`. -/
#check (x' : GroupoidsOver.slice T' ⟶ X)
