module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap94.«94_9_8_1_Comparison»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Scheme tests versus algebraic-space tests for representable morphisms

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on algebraic-space base changes of a
morphism of algebraic stacks representable by algebraic spaces, not only on
scheme base changes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 100.3.2: Let `P` be a property of morphisms of algebraic spaces that is
fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Then `f` has `P`
if and only if for every algebraic space `Z` and morphism `Z.toGroupoids ⟶ Y`,
every morphism of algebraic spaces representing `Z ×_Y X ⟶ Z` has `P`. -/
@[stacks 04XC]
theorem has_iff_forall_algebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has P f ↔
      ∀ (Z : AlgebraicSpace S) (z : Z.toGroupoids ⟶ Y) (W : AlgebraicSpace S)
        (w : W ⟶ Z), RepresentsTwoFibreProductOnSpace f z W Z w → P w :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
