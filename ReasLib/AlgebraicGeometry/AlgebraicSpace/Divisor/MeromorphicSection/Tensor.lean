/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.ClassGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Order.Tensor

/-!
# Additivity of Weil divisors of meromorphic sections

On a locally Noetherian integral algebraic space, the Weil divisor of a tensor of
regular meromorphic sections is the sum of the Weil divisors, and the Weil divisor
class of a tensor of invertible modules is the sum of the classes. Extending
these constructions to ringed sites requires corresponding divisor theory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The Weil divisor of the tensor of regular meromorphic sections of invertible
modules is the sum of their Weil divisors. -/
theorem nonzeroMeromorphicSectionWeilDivisor_tensor
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t) :
    nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
      (isRegularMeromorphicSection_tensor s t hs ht) =
      nonzeroMeromorphicSectionWeilDivisor s hs +
        nonzeroMeromorphicSectionWeilDivisor t ht :=
  sorry

/-- The coefficient of the Weil divisor of a tensor of regular meromorphic sections along a
prime divisor is the sum of the coefficients of the factors. -/
theorem nonzeroMeromorphicSectionWeilDivisor_tensor_coeff
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t)
    (Z : PrimeDivisor X) :
    (nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
        (isRegularMeromorphicSection_tensor s t hs ht)).coeff Z =
      (nonzeroMeromorphicSectionWeilDivisor s hs).coeff Z +
        (nonzeroMeromorphicSectionWeilDivisor t ht).coeff Z :=
  sorry

/-- The Weil divisor class of a tensor of invertible modules is the sum of their
Weil divisor classes. -/
theorem invertibleModuleWeilDivisorClass_tensor
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N] :
    invertibleModuleWeilDivisorClass (L ⊗ N) =
      invertibleModuleWeilDivisorClass L + invertibleModuleWeilDivisorClass N :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
