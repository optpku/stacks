module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally Noetherian targets upgrade finite type to finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks which is locally of finite type, with
locally Noetherian target, is locally of finite presentation. -/
@[stacks 0DQJ]
instance locallyOfFinitePresentation_of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- A morphism of algebraic stacks which is of finite type and quasi-separated,
with locally Noetherian target, is of finite presentation. -/
@[stacks 0DQJ]
instance finitePresentation_of_finiteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f] :
    FinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
