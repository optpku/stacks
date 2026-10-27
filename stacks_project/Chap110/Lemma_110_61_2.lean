/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.ShiftedSingle
import StacksCheckRecall

/-!
# Coproducts of shifted locally quasi-coherent modules agree with products
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open Limits

universe u

/- Lemma 110.61.2: if `X` is an algebraic stack and `F n` is a collection of
locally quasi-coherent sheaves with the flat base change property on `X`, then
the canonical map `∐ shiftSingle F ⟶ ∏ᶜ shiftSingle F` is an isomorphism in
`D(𝒪_X)`. -/
@[stacks 08IZ]
#check (AlgebraicGeometry.AlgebraicStack.shiftSingle_coproductToProduct_isIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : ℕ → fppfModules X) (hF : ∀ n, FppfModules.lqcohFbc X (F n))
    [HasCoproduct (shiftSingle F)] [HasProduct (shiftSingle F)],
    IsIso (coproductToProduct (shiftSingle F)))

