module

public import stacks_project.Chap101.Definition_101_16_2_SmoothLocal

/-!
# Monotonicity of smooth-local-on-source-and-target morphisms of algebraic stacks

If two morphism properties of algebraic spaces are smooth local on the
source-and-target and one implies the other, then the same implication holds
for their lifts to morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- Remark 101.16.5: if `P` and `P'` are morphism properties of algebraic
spaces that are smooth local on the source-and-target and `P ≤ P'`, then the
lifts of `P` and `P'` to morphisms of algebraic stacks from Definition 101.16.2
satisfy the same implication. In particular, if `f : X ⟶ Y` has
`hasSmoothLocalAtSourceAndTarget P`, then it has
`hasSmoothLocalAtSourceAndTarget P'`. -/
@[stacks 06PS]
theorem of_le {S : Scheme.{u}} {P P' : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P'] (h : P ≤ P')
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (hf : hasSmoothLocalAtSourceAndTarget P f) :
    hasSmoothLocalAtSourceAndTarget P' f :=
  sorry

end hasSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
