module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness

/-!
# Valuative criterion of separatedness for algebraic stacks

A quasi-separated morphism of algebraic stacks that satisfies uniqueness in the
valuative criterion is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- A quasi-separated morphism of algebraic stacks that satisfies the uniqueness
part of the valuative criterion is separated. -/
@[stacks 0CLT, instance 100]
theorem of_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] [ValuativeCriterion.Uniqueness f] : Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Separated
