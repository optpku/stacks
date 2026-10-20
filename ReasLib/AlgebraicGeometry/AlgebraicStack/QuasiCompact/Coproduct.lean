module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-!
# Finite coproducts of quasi-compact algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

noncomputable section

namespace AlgebraicGeometry.AlgebraicStack

/-- A finite disjoint union of quasi-compact algebraic stacks is a quasi-compact
algebraic stack. -/
instance instIsQuasiCompact_coproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)]
    [∀ i, IsQuasiCompact (X i)] :
    IsQuasiCompact (GroupoidsOver.coproduct X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
