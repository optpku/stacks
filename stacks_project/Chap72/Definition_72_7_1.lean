/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Order
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open scoped nonZeroDivisors

universe u

/- Definition 72.7.1: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module. Let
`s ∈ Γ(X, 𝒦_X(L))` be a regular meromorphic section of `L`. For every prime
divisor `Z ⊂ X` with generic point `ξ ∈ |Z|`, the order of vanishing of `s`
along `Z` is the integer
`ord_{Z, L}(s) = length (O_{X,ξ}^h ⧸ a) - length (O_{X,ξ}^h ⧸ b)`
where `a, b ∈ O_{X,ξ}^h` are nonzerodivisors such that `s / s_ξ = a / b` in
`Q(O_{X,ξ}^h)`. -/
@[stacks 0EPR] #check (AlgebraicGeometry.AlgebraicSpace.MeromorphicSection.ord_eq_length :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : MeromorphicSection.henselianFraction s hs Z =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩),
    MeromorphicSection.ord s hs Z =
      ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ))
