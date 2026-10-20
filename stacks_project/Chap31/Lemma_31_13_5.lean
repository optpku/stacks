/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension

open AlgebraicGeometry

universe u

/- Lemma 31.13.5: if `D ⊆ X` is an effective Cartier divisor and `x ∈ D`, then finite
local dimension at `x` on `X` forces the local dimension on `D` at `x` to be strictly smaller. -/
@[stacks 056N] #check
  (AlgebraicGeometry.IsEffectiveCartierDivisor.ringKrullDim_subscheme_stalk_lt :
    ∀ {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
      (x : D.subscheme),
      ringKrullDim (X.presheaf.stalk (D.subschemeι.base x)) < ⊤ →
        ringKrullDim (D.subscheme.presheaf.stalk x) <
          ringKrullDim (X.presheaf.stalk (D.subschemeι.base x)))
