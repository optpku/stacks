/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_11_3_Comparison
public import stacks_project.Chap93.Lemma_93_11_3_Trivial

/-!
# Infinitesimal automorphisms and tangent space of `Def_X`

In Example 93.11.1, `Inf(Def_X)` identifies with
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`,
and `T Def_X` identifies with `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open FlatAlgebraicSpaceCat

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- Lemma 93.11.3 (1)
In Example 93.11.1 let `X` be an algebraic space over `k`. Then `Inf(Def_X)` equals
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`, as bijectivity of `infToExtZero`. -/
@[stacks 0E41]
theorem infToExtZero_bijective :
    Function.Bijective (infToExtZero Λ k X) := sorry

/-- Lemma 93.11.3 (2)
In Example 93.11.1 let `X` be an algebraic space over `k`. Then
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` equals `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, as bijectivity of
`extZeroEquivHomOmega`. -/
@[stacks 0E41]
theorem extZeroEquivHomOmega_bijective :
    Function.Bijective (extZeroEquivHomOmega Λ k X) := sorry

/-- Lemma 93.11.3 (3)
In Example 93.11.1 let `X` be an algebraic space over `k`. Then
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` equals `Der_k(𝒪_X, 𝒪_X)`, as bijectivity of
`homOmegaEquivDer`. -/
@[stacks 0E41]
theorem homOmegaEquivDer_bijective :
    Function.Bijective (homOmegaEquivDer Λ k X) := sorry

/-- Lemma 93.11.3 (4)
In Example 93.11.1 let `X` be an algebraic space over `k`. Then `T Def_X` equals
`Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`, as bijectivity of `ofExtOne`. -/
@[stacks 0E41]
theorem ofExtOne_bijective :
    Function.Bijective (ofExtOne Λ k X) := sorry

end FlatAlgebraicSpaceCat
