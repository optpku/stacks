/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Order
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.6.4: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. For every prime
divisor `Z ⊂ X` with generic point `ξ ∈ |Z|`, the order of vanishing of `f`
along `Z` is the integer
`Z.ord f = length (O_{X,ξ}^h ⧸ a) - length (O_{X,ξ}^h ⧸ b)`
where `a, b ∈ O_{X,ξ}^h` are nonzerodivisors such that the image of `f` in
`Q(O_{X,ξ}^h)` equals `a / b`. This is well defined by Algebra, Lemma 10.121.1. -/
@[stacks 0ENL] #check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.ord :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
      (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ), ℤ)
