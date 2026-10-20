/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.Components
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 41.21.2: for a locally Noetherian scheme, an effective Cartier divisor has strict
normal crossings exactly when it is reduced, its reduced irreducible components are effective
Cartier divisors, and every finite nonempty component intersection is regular of the expected
ambient codimension. -/
@[stacks 0BIA] #check
  (AlgebraicGeometry.isStrictNormalCrossingsDivisor_iff_components :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι],
      IsStrictNormalCrossingsDivisor D ↔
        IsReduced D.subscheme ∧
          (∀ i : irreducibleComponents D.subscheme,
            IsEffectiveCartierDivisor (D.reducedComponent i).subschemeι) ∧
            ∀ J : Finset (irreducibleComponents D.subscheme), J.Nonempty →
              Scheme.Regular (D.componentIntersection J).subscheme ∧
                ∀ ξ : (D.componentIntersection J).subscheme,
                  ξ ∈ genericPoints (D.componentIntersection J).subscheme →
                    ringKrullDim
                        (X.presheaf.stalk ((D.componentIntersection J).subschemeι.base ξ)) =
                      J.card)
