module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.TwoFibreProduct
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
`H_d(X'/Y) ⟶ H_d(X/Y)` induced by `G : X' ⟶ X`.
The source defines finite Hilbert stacks for `d ≥ 1`; the concrete construction
here also supports rank zero and is stated for every natural rank. -/
@[stacks 05YK] #check (AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (FiniteHilbertStack.toGroupoids F d).p.Fiber U), GroupoidsOver S)
