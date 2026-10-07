module

public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Lemma_100_6_3_Coproduct

/-!
# Finite coproducts of quasi-compact algebraic stacks

A finite disjoint union of quasi-compact algebraic stacks is again
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

noncomputable section

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.6.3: a finite disjoint union of quasi-compact algebraic stacks is a
quasi-compact algebraic stack. -/
@[stacks 04YD, instance]
instance instIsQuasiCompact_coproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)]
    [∀ i, IsQuasiCompact (X i)] :
    IsQuasiCompact (GroupoidsOver.coproduct X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
