/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Open immersions of algebraic stacks are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.8: An open immersion of algebraic stacks is locally of finite
presentation. -/
@[stacks 06Q7]
instance locallyOfFinitePresentation_of_openImmersion {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
