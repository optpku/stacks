module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Noetherian valuative criterion for universal closedness of algebraic stacks

A finite-type morphism of algebraic stacks into a locally Noetherian target is
universally closed as soon as every DVR valuative square admits a dominating
valuation-ring extension with a nonempty dotted-arrow category.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

/-- A finite-type morphism `f : X ⟶ Y` of algebraic stacks
over a scheme `S` with `Y` locally Noetherian is universally closed whenever
every 2-commutative valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` with
`A` a discrete valuation ring and `K` its field of fractions admits a field
extension `K'/K` and a valuation ring `A' ⊂ K'` dominating `A` whose induced
dotted-arrow category is nonempty. -/
@[stacks 0H2C]
instance of_existsExtension {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.ExistsExtension f] : UniversallyClosed f :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
