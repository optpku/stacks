/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- At the generic point of an integral effective Cartier divisor on a locally Noetherian
scheme, the ambient local ring is a domain. -/
instance instIsDomainAmbientStalkAtGenericPoint [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsIntegral D.subscheme] :
    IsDomain (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := sorry

/-- At the generic point of an integral effective Cartier divisor on a locally Noetherian
scheme, the ambient local ring is a discrete valuation ring. -/
instance instIsDiscreteValuationRingAmbientStalkAtGenericPoint [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsIntegral D.subscheme] :
    IsDiscreteValuationRing
      (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
