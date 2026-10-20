module

public import stacks_project.Chap72.Definition_72_7_1_Order
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 72.7.1: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module. Let
`s ∈ Γ(X, 𝒦_X(L))` be a regular meromorphic section of `L`. For every prime
divisor `Z ⊂ X` with generic point `ξ ∈ |Z|`, the order of vanishing of `s`
along `Z` is the integer
`ord_{Z, L}(s) = length (O_{X,ξ}^h ⧸ a) - length (O_{X,ξ}^h ⧸ b)`
where `a, b ∈ O_{X,ξ}^h` are nonzerodivisors such that `s / s_ξ = a / b` in
`Q(O_{X,ξ}^h)`. -/
@[stacks 0EPR] #check MeromorphicSection.ord
