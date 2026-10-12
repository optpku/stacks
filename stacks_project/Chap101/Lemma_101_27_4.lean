/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation
public import stacks_project.Chap101.Definition_101_37_1_FiniteType

/-!
# Finite presentation morphisms of algebraic stacks are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.4 (1): A morphism of algebraic stacks which is locally of finite
presentation is locally of finite type. -/
@[stacks 06Q5]
instance locallyOfFiniteType_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f :=
  sorry

/-- Lemma 101.27.4 (2): A morphism of algebraic stacks of finite presentation is
of finite type. -/
@[stacks 06Q5]
instance finiteType_of_finitePresentation {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [FinitePresentation f] :
    FiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
