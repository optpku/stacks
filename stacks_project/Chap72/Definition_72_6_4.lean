module

public import stacks_project.Chap72.Definition_72_6_4_Order
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 72.6.4: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. For every prime
divisor `Z ⊂ X` with generic point `ξ ∈ |Z|`, the order of vanishing of `f`
along `Z` is the integer
`Z.ord f = length (O_{X,ξ}^h ⧸ a) - length (O_{X,ξ}^h ⧸ b)`
where `a, b ∈ O_{X,ξ}^h` are nonzerodivisors such that the image of `f` in
`Q(O_{X,ξ}^h)` equals `a / b`. This is well defined by Algebra, Lemma 10.121.1. -/
@[stacks 0ENL] #check PrimeDivisor.ord
