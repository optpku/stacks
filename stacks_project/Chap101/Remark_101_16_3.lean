module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap101.Definition_101_16_2_SmoothLocal

/-!
# Composition of smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and stable under composition, then so is its lift to
morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- Remark 101.16.3: if a morphism property `P` of algebraic spaces is smooth
local on the source-and-target and stable under composition, then the lift of
`P` to morphisms of algebraic stacks from Definition 101.16.2 is also stable
under composition. In particular, if `f : X ⟶ Y` and `g : Y ⟶ Z` have
`hasSmoothLocalAtSourceAndTarget P`, then so does `f ≫ g` (source `g ∘ f`). -/
@[stacks 06FP]
theorem comp {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : hasSmoothLocalAtSourceAndTarget P f)
    (hg : hasSmoothLocalAtSourceAndTarget P g) :
    hasSmoothLocalAtSourceAndTarget P (f ≫ g) :=
  sorry

end hasSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
