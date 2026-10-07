module

public import stacks_project.Chap97.«97_15_0_1_RelativeMap»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory CategoryTheory.TwoFibreProduct

/- 97.15.0.1: for an object ξ of H_d(X/Y) along a 1-morphism F : X ⟶ Y, the pair
(x, α) induces the 1-morphism
  (Sch/Z)_fppf ⟶ (Sch/U)_fppf ×_{y, Y, F} X
by the 2-fibre-product universal property. This is
`FiniteHilbertStack.relativeMap F ξ` from `GroupoidsOver.slice ξ.Z` to
`relativeApex F ξ`. Choosing an algebraic space X_y over U representing that
2-fibre product, the same data yields
`relativeSpaceHom : ofOver ξ.Z ⟶ X_y` of algebraic spaces over U.
The two displayed diagrams are the commuting triangle of spaces
  ofOver ξ.Z ⟶ X_y over ofOver ξ.U
and the 2-fibre-product square of stacks with apex `relativeApex F ξ`,
first projection `TwoFibreProduct.fst`, second projection `TwoFibreProduct.snd`,
and 2-cell `relativeMapIso`. -/
@[stacks 06CK] #check AlgebraicGeometry.FiniteHilbertStack.relativeMap
