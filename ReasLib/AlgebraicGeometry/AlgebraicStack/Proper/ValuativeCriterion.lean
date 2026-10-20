module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-!
# Valuative criterion for properness of algebraic stacks

A finite-type quasi-separated morphism of algebraic stacks is proper if and
only if it satisfies both the uniqueness and existence parts of the valuative
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- A finite-type quasi-separated morphism of algebraic stacks is proper if and
only if it satisfies both the uniqueness and existence parts of the valuative
criterion. -/
theorem iff_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    Proper f ↔ ValuativeCriterion.Uniqueness f ∧ ValuativeCriterion.Existence f :=
  sorry

/-- A finite-type quasi-separated morphism of algebraic stacks that satisfies
both the uniqueness and existence parts of the valuative criterion is proper. -/
instance of_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Existence f] :
    Proper f :=
  (iff_valuativeCriterion f).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicStack.Proper
