/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of local finite presentation against locally finite type postcomposition

If a composite morphism of algebraic spaces is locally of finite presentation and
the second factor is locally of finite type, then the first factor is locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFinitePresentation

/-- If a composite morphism of algebraic spaces is locally of finite presentation
and the second factor is locally of finite type, then the first factor is
locally of finite presentation. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := sorry

end LocallyOfFinitePresentation

/-- Locally of finite presentation morphisms of algebraic spaces cancel against a
locally of finite type postcomposition. -/
instance locallyOfFinitePresentation_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (@LocallyOfFiniteType S) := sorry

end AlgebraicGeometry.AlgebraicSpace
