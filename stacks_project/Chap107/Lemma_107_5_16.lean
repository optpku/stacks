/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary

/-!
# Pseudo-catenary algebraic stacks along locally of finite type morphisms

A morphism of algebraic stacks that is locally of finite type into a
pseudo-catenary locally Noetherian target has pseudo-catenary source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.16: if `X` is a pseudo-catenary locally Noetherian algebraic
stack and `f : Y ⟶ X` is locally of finite type, then there exists a smooth
surjective morphism `V ⟶ Y` whose source is a universally catenary scheme,
hence `Y` is pseudo-catenary. -/
@[stacks 0DRW]
theorem IsPseudoCatenary.of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [IsLocallyNoetherian X] [IsPseudoCatenary X] (f : Y ⟶ X)
    [LocallyOfFiniteType f] : IsPseudoCatenary Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
