module

public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism
public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Comparison of thickenings of algebraic stacks

A thickening of algebraic stacks in the abuse-of-language sense is equivalent
to a 1-morphism representable by algebraic spaces that is a thickening in the
sense of scheme-slice tests, and such a morphism is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- A morphism of algebraic stacks is a thickening if and only if it is
representable by algebraic spaces and has the algebraic-space thickening
property in the sense of scheme-slice tests. -/
theorem iff_has {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsThickening i ↔ relativelyRepresentableByAlgebraicSpaces i ∧
      has (@AlgebraicSpace.IsThickening S) i := sorry

/-- A 1-morphism of algebraic stacks which is representable by algebraic spaces
and has the algebraic-space thickening property is a thickening. -/
theorem of_has {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    (hf : relativelyRepresentableByAlgebraicSpaces i)
    (h : has (@AlgebraicSpace.IsThickening S) i) : IsThickening i := sorry

/-- A thickening of algebraic stacks has the algebraic-space thickening
property on scheme-slice representing morphisms. -/
theorem has_isThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    has (@AlgebraicSpace.IsThickening S) i := sorry

/-- A thickening of algebraic stacks is a universal homeomorphism. -/
instance instUniversalHomeomorphism {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    UniversalHomeomorphism i := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
