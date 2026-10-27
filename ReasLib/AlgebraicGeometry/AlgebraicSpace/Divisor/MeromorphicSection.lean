/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.LocallyFinite


/-! # Weil divisors of regular meromorphic sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite PresheafOfModules
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The Weil divisor of a regular meromorphic section, with coefficients given by
the imported henselian section order. -/
def nonzeroMeromorphicSectionWeilDivisor {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    WeilDivisor X :=
  WeilDivisor.ofCoeff X (fun Z ↦ MeromorphicSection.ord s hs Z)
    (locallyFinite_regularMeromorphicSectionOrder_ne_zero X s hs)

/-- The coefficient of the section divisor is its henselian section order. -/
theorem nonzeroMeromorphicSectionWeilDivisor_coeff {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (Z : PrimeDivisor X) :
    (nonzeroMeromorphicSectionWeilDivisor s hs).coeff Z = MeromorphicSection.ord s hs Z := sorry

end AlgebraicGeometry.AlgebraicSpace
