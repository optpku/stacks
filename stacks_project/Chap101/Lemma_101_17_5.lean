/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Locally of finite type over locally Noetherian algebraic stacks

A morphism of algebraic stacks that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Lemma 101.17.5. Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `f`
is locally of finite type and `Y` is locally Noetherian, then `X` is locally
Noetherian. -/
@[stacks 06R6]
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
