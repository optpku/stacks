module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Separated
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.11.4: a locally finite-type quasi-separated morphism to a locally
Noetherian algebraic stack is separated if DVR uniqueness holds along a dense
finite-type morphism. -/
@[stacks 0E95] #check
  (AlgebraicGeometry.AlgebraicStack.Separated.of_uniquenessAlong :
    ∀ {S : Scheme.{u}} {U X Y : GroupoidsOver S}
      [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) (h : U ⟶ X)
      [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f] [FiniteType h],
      DenseRange (Points.map h) → ValuativeCriterion.DVR.Along.Uniqueness h f →
        Separated f)
