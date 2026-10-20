module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.Noetherian
import StacksCheckRecall

/-!
# Locally Noetherian targets upgrade finite type to finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.5 (1): A morphism of algebraic stacks which is locally of finite
type, with locally Noetherian target, is locally of finite presentation. -/
@[stacks 0DQJ]
#check (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f],
      LocallyOfFinitePresentation f)

/- Lemma 101.27.5 (2): A morphism of algebraic stacks which is of finite type
and quasi-separated, with locally Noetherian target, is of finite
presentation. -/
@[stacks 0DQJ]
#check (AlgebraicGeometry.AlgebraicStack.finitePresentation_of_finiteType :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f],
      FinitePresentation f)

end AlgebraicGeometry.AlgebraicStack
