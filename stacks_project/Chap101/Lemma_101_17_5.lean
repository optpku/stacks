module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Noetherian
import StacksCheckRecall

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

/- Lemma 101.17.5. A locally-of-finite-type morphism of algebraic stacks
with locally Noetherian target has locally Noetherian source. -/
@[stacks 06R6] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsLocallyNoetherian Y],
      IsLocallyNoetherian X)

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
