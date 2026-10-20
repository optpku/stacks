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

/- Lemma 31.15.3 (1): a generic point of a locally principal closed subscheme has ambient
stalk dimension at most one. -/
@[stacks 0BCN] #check
  (AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme.ringKrullDim_stalk_le_one_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
      [IsLocallyPrincipalClosedSubscheme D.subschemeι] {ξ : D.subscheme},
      ξ ∈ genericPoints D.subscheme →
        ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) ≤ 1)

/- Lemma 31.15.3 (2): a generic point of an effective Cartier divisor has ambient stalk
dimension one. -/
@[stacks 0BCN] #check
  (AlgebraicGeometry.IsEffectiveCartierDivisor.ringKrullDim_stalk_eq_one_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι] {ξ : D.subscheme},
      ξ ∈ genericPoints D.subscheme →
        ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) = 1)
