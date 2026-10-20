/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal.Complement

/-!
# Complements of effective Cartier divisors

The open complement of an effective Cartier divisor on an algebraic space is
an affine morphism into the ambient space, and is scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.6.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `i : D ⟶ X` is an effective Cartier divisor, then the open complement
inclusion `closedImmersionComplementι i` is affine and scheme-theoretically
dense in `X`. -/
@[stacks 083S] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.schemeTheoreticallyDense_closedImmersionComplementι :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
      [IsEffectiveCartierDivisor i],
      IsSchemeTheoreticallyDense (closedImmersionComplementι i))

section

variable {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
  [IsEffectiveCartierDivisor i]

/- Effective Cartier divisors are locally principal, so the canonical affine
complement instance also gives the affine conclusion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal.affine_closedImmersionComplementι i :
    Affine (closedImmersionComplementι i))

end
