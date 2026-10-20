module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Regular.Singleton
import StacksCheckRecall

/-!
# Regularity of reduced locally Noetherian singleton algebraic stacks

A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.11.10: A reduced, locally Noetherian algebraic stack whose space
of points is a singleton is regular. -/
@[stacks 06MV] #check
  (AlgebraicGeometry.AlgebraicStack.isRegular_of_isReduced_isLocallyNoetherian_subsingleton :
    ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
      [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)],
      IsRegular Z)

end AlgebraicGeometry.AlgebraicStack
