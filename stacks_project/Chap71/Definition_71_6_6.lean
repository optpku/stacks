/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_6_6_Sum
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.6.6
Let `S` be a scheme and let `X` be an algebraic space over `S`. Given effective
Cartier divisors `D₁`, `D₂` on `X`, the sum `D = D₁ + D₂` is the closed subspace
of `X` corresponding to the quasi-coherent sheaf of ideals
`IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf ⊂ 𝒪_X`.
-/
@[stacks 083U] #check effectiveCartierDivisorSum

#check effectiveCartierDivisorSum_spec

#check IdealSubobject.mul

#check effectiveCartierDivisorSum_eq

#check effectiveCartierDivisorSum_idealSheaf
