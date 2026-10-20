/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection

/-!
# Quotients of meromorphic sections

The quotient of two nonzero meromorphic sections of the same invertible module is a function-field
unit. Its principal divisor measures the difference of the associated Weil divisors.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- A function-field unit is the quotient of two meromorphic sections when the generic germ of
the numerator is obtained by scaling the generic germ of the denominator by that unit. -/
def IsMeromorphicSectionQuotient
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (f : X.functionFieldˣ) : Prop :=
  SheafOfModules.sectionGermOfCommRing s (genericPoint X) =
    algebraMap X.functionField
      ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.stalk (genericPoint X))
      (f : X.functionField) •
        SheafOfModules.sectionGermOfCommRing t (genericPoint X)

/-- The function-field unit obtained by dividing one nonzero meromorphic section of an invertible
module by another. -/
noncomputable def meromorphicSectionQuotient
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) : X.functionFieldˣ :=
  @dite X.functionFieldˣ
    (∃! f : X.functionFieldˣ, IsMeromorphicSectionQuotient X L s t f)
    (Classical.propDecidable _)
    (fun h ↦ Classical.choose h.exists)
    (fun _ ↦ 1)

/-- The chosen quotient of two nonzero meromorphic sections satisfies the generic-germ quotient
equation. -/
theorem meromorphicSectionQuotient_spec
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    IsMeromorphicSectionQuotient X L s t
      (meromorphicSectionQuotient X L s t hs ht) := sorry

/-- A function-field unit is the quotient of two nonzero meromorphic sections exactly when it is
the chosen quotient. -/
theorem isMeromorphicSectionQuotient_iff_eq
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) (f : X.functionFieldˣ) :
    IsMeromorphicSectionQuotient X L s t f ↔
      f = meromorphicSectionQuotient X L s t hs ht := sorry

/-- The Weil divisor of a nonzero meromorphic section equals the Weil divisor of another nonzero
section of the same invertible module plus the principal divisor of their quotient. -/
theorem nonzeroMeromorphicSectionWeilDivisor_eq_add_principal
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    nonzeroMeromorphicSectionWeilDivisor X L s hs =
      nonzeroMeromorphicSectionWeilDivisor X L t ht +
        principalWeilDivisor X (meromorphicSectionQuotient X L s t hs ht) := sorry

end AlgebraicGeometry.Scheme
