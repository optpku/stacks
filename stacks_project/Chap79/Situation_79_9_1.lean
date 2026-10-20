module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

section

variable {S : Scheme.{u}} {k : Type u} [Field k]
variable (σ : Spec (CommRingCat.of k) ⟶ S)
variable (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))

/- Situation 79.9.1: here `S` is a scheme, `k` is a field over `S` via
`σ : Spec (CommRingCat.of k) ⟶ S`, and `(G, m)` is a group algebraic space
over `Spec(k)` with `m = μ[G.X]`. -/
@[stacks 06DX] #check
  (AlgebraicGeometry.GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)) : Type (u + 1))

@[stacks 06DX] #check
  (CategoryTheory.MonObj.mul (X := G.X) : G.X ⊗ G.X ⟶ G.X)

end
