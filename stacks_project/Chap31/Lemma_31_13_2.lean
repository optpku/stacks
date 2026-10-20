/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine

open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/- Lemma 31.13.2: an ideal-sheaf presentation of a closed subscheme is an effective Cartier
divisor exactly when, near every point of its support, its ideal is generated on an affine open
by one nonzerodivisor. -/
@[stacks 01WS] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartierDivisor_iff_affineLocalNonZeroDivisorGenerator :
    ∀ {S : Scheme.{u}} (D : S.IdealSheafData),
      AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ↔
        ∀ x : S, x ∈ D.support →
          ∃ U : S.affineOpens, x ∈ (U : S.Opens) ∧
            ∃ f : Γ(S, U),
              f ∈ nonZeroDivisors (Γ(S, U)) ∧
                D.ideal U = Ideal.span ({f} : Set (Γ(S, U))))
