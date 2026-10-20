module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.FieldExtension
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.2.5: A versal ring at a finite-type field-valued point extends
along a finite field extension through an S-algebra map inducing that extension
and formally smooth for the target maximal-adic topology. -/
@[stacks 0DQY] #check (AlgebraicGeometry.AlgebraicStack.exists_isVersalRing_restrict :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A],
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ φ : CompleteLocalSAlgebra.Hom A' A,
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
              (x0.restrict l).structureHom)

end AlgebraicGeometry.AlgebraicStack
