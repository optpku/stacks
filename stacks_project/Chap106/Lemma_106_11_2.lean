module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Separated
import StacksCheckRecall

/-!
# Noetherian valuative criterion for separatedness of algebraic stacks

A locally of finite type quasi-separated morphism of algebraic stacks into a
locally Noetherian target is separated as soon as every DVR valuative 2-square
has dotted-arrow category empty or a setoid with exactly one isomorphism class.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.11.2: a locally of finite type, quasi-separated morphism with locally
Noetherian target is separated if every DVR valuative square has dotted-arrow
category either empty or a setoid with exactly one isomorphism class. -/
@[stacks 0E80] #check (AlgebraicGeometry.AlgebraicStack.Separated.of_dvrUniqueness :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.DVR.Uniqueness f], Separated f)

end AlgebraicGeometry.AlgebraicStack
