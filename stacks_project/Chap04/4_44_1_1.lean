module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

@[expose] public section


universe w v u

namespace CategoryTheory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T X Y : B}
variable (j : S ⟶ T) (x : S ⟶ X) (f : X ⟶ Y) (y : T ⟶ Y)
variable (γ : j ≫ y ≅ x ≫ f)
variable (a : T ⟶ X)

/- The source-facing datum here is the solid `2`-commutative boundary together with its displayed
diagonal type. `Bicategory.PseudoPullbackCone` is the exact existing owner for the boundary
and chosen `γ`; mathlib's `LeftLift` owns only one triangular comparison, while `DottedArrow` from
Definition 4.44.1 adds comparisons and coherence not asserted by this equation. We therefore check
the specialized square and the explicit `a : T ⟶ X` separately. The only generalization is from a
`(2,1)`-category to a bicategory: the source is recovered by adding
`[Bicategory.IsLocallyGroupoid B]`, and no diagram field uses it. This keeps the reusable square
data available without duplicating the later dotted-arrow owner. -/

/- 4.44.1.1: the solid boundary maps `j`, `x`, `f`, and `y`, with the chosen witness
`γ : j ≫ y ≅ x ≫ f`, form the `2`-commutative square in the displayed dotted-arrow diagram. -/
@[stacks 0H19 "solid 2-commutative square in a dotted-arrow diagram"]
#check (⟨S, j, x, γ⟩ : Bicategory.PseudoPullbackCone y f)

/- Companion check: the dotted diagonal in 4.44.1.1 has source `T` and target `X`. -/
#check (a : T ⟶ X)

end CategoryTheory
