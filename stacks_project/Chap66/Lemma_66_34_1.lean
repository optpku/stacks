module

public import stacks_project.Chap66.Lemma_66_34_1_Quotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.34.1: if `S` is a scheme, `X` is an algebraic space over `S`, and an
abstract group `G` acts freely on `X` via `ρ : G →* Aut X`, then the fppf sheaf
associated to `T ↦ X(T)/G` is an algebraic space. -/
@[stacks 071S]
#check AlgebraicGeometry.AlgebraicSpace.quotientSheaf_spec
