module

public import stacks_project.Chap97.«97_12_6_1_Map»
public import stacks_project.Chap97.«97_12_6_1_Pullback»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory CategoryTheory.TwoFibreProduct

/- 97.12.6.1: the displayed 2-fibre product
`(Sch/U)_fppf ×_{ξ, ℋ_d(𝒳/𝒴)} ℋ_d(𝒳'/𝒴)` is
`FiniteHilbertStack.twoFibreProduct G F d ξ` in `GroupoidsOver S`.
Here `GroupoidsOver.slice U` is `(Sch/U)_fppf`, `ξ` is an object of
`H_d(X/Y)` over `U`, and `map G F d` is the 1-morphism
`H_d(X'/Y) ⟶ H_d(X/Y)` induced by `G : X' ⟶ X`. -/
@[stacks 05YK] #check AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct
