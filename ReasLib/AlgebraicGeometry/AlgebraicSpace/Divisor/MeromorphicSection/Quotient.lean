/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Quotient

/-!
# Quotients of meromorphic section divisors

The quotient of two regular meromorphic sections of an invertible module is a
rational-function unit whose principal divisor measures the difference of their
section divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The order identity is the coefficientwise form of the divisor comparison. -/
theorem nonzeroMeromorphicSectionWeilDivisor_eq_add_principal_coeff
    {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) (Z : PrimeDivisor X) :
    MeromorphicSection.ord s hs Z =
      MeromorphicSection.ord t ht Z +
        Z.ord (meromorphicSectionQuotient s t hs ht) :=
  sorry

/-- The Weil divisor of one regular meromorphic section differs from that of
another by the principal divisor of their rational-function quotient. -/
theorem nonzeroMeromorphicSectionWeilDivisor_eq_add_principal
    {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) :
    nonzeroMeromorphicSectionWeilDivisor s hs =
      nonzeroMeromorphicSectionWeilDivisor t ht +
        principalWeilDivisor X (meromorphicSectionQuotient s t hs ht) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
