module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing.MeromorphicSection.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.RegularAt

/-!
# Weil divisors of nonzero meromorphic sections

A nonzero meromorphic section of an invertible module on a locally Noetherian integral scheme
has an intrinsic order along every prime divisor.  These orders define its Weil divisor and its
class modulo principal Weil divisors.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

/-- The supports of prime divisors where a nonzero meromorphic section does not come from the
module stalk at the generic point form a locally finite family. -/
theorem locallyFinite_primeDivisors_nonzeroMeromorphicSection_not_regularAt
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ AlgebraicGeometry.LocallyRingedSpace.MeromorphicSection.IsRegularAt
          s Z.genericPoint ∧ x ∈ (Z.support : Set X)} := sorry

/-- The coefficient at a prime divisor of the Weil divisor associated to a nonzero meromorphic
section of an invertible module. -/
noncomputable def nonzeroMeromorphicSectionWeilDivisorCoeff
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0)
    (Z : PrimeDivisor X) : ℤ :=
  regularMeromorphicSectionOrderAlongPrimeDivisor s
    ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero L s).2 hs) Z

/-- The divisor coefficient of a nonzero meromorphic section is its intrinsic order along the
prime divisor. -/
theorem nonzeroMeromorphicSectionWeilDivisorCoeff_def
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0)
    (Z : PrimeDivisor X) :
    nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z =
      regularMeromorphicSectionOrderAlongPrimeDivisor s
        ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero L s).2 hs) Z :=
  rfl

/-- The supports of prime divisors on which a nonzero meromorphic section has nonzero order form
a locally finite family. -/
theorem locallyFinite_nonzeroMeromorphicSectionWeilDivisorCoeff_ne_zero
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

variable (X)

/-- The Weil divisor associated to a nonzero meromorphic section of an invertible module. -/
noncomputable def nonzeroMeromorphicSectionWeilDivisor
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) : Div(X) :=
  WeilDivisor.ofCoeff X
    (fun Z ↦ nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z)
    (locallyFinite_nonzeroMeromorphicSectionWeilDivisorCoeff_ne_zero L s hs)

/-- The coefficient of the Weil divisor of a nonzero meromorphic section is its intrinsic order
along the prime divisor. -/
@[simp]
theorem nonzeroMeromorphicSectionWeilDivisor_coeff
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0)
    (Z : PrimeDivisor X) :
    (nonzeroMeromorphicSectionWeilDivisor X L s hs).coeff Z =
      nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z :=
  rfl

/-- The Weil divisor class associated to a nonzero meromorphic section of an invertible module. -/
noncomputable def nonzeroMeromorphicSectionWeilDivisorClass
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) : Cl(X) :=
  weilDivisorClassGroupMk X (nonzeroMeromorphicSectionWeilDivisor X L s hs)

/-- The class of a nonzero meromorphic section is the image of its Weil divisor under the
canonical quotient homomorphism. -/
@[simp]
theorem nonzeroMeromorphicSectionWeilDivisorClass_def
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) :
    nonzeroMeromorphicSectionWeilDivisorClass X L s hs =
      weilDivisorClassGroupMk X (nonzeroMeromorphicSectionWeilDivisor X L s hs) :=
  rfl

namespace nonzeroMeromorphicSectionWeilDivisorCoeff

/-- The coefficient functions of the divisors of two nonzero meromorphic sections of the same
invertible module differ by the orders of a function-field unit. -/
theorem exists_functionFieldUnit_sub
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ f : X.functionFieldˣ,
      ∀ Z : PrimeDivisor X,
        nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z =
          nonzeroMeromorphicSectionWeilDivisorCoeff L t ht Z +
            X.ord (f : X.functionField) Z.genericPoint := sorry

end nonzeroMeromorphicSectionWeilDivisorCoeff

/-- The Weil divisor class associated to an invertible module is independent of the chosen
nonzero meromorphic section. -/
theorem nonzeroMeromorphicSectionWeilDivisorClass_eq
    (L : X.Modules) [Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    nonzeroMeromorphicSectionWeilDivisorClass X L s hs =
      nonzeroMeromorphicSectionWeilDivisorClass X L t ht := sorry

/-- The Weil divisor of the tensor product of nonzero meromorphic sections is the sum of their
Weil divisors. -/
theorem nonzeroMeromorphicSectionWeilDivisor_tensor
    {L N : X.Modules} [Modules.Invertible L] [Modules.Invertible N]
    (s : X.toLocallyRingedSpace.meromorphicSections L)
    (t : X.toLocallyRingedSpace.meromorphicSections N)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    (@nonzeroMeromorphicSectionWeilDivisor X _ _ (L ⊗ N)
        (isInvertibleObject.tensor L N)
        (X.toLocallyRingedSpace.meromorphicSectionTensor s t)
        (AlgebraicGeometry.meromorphicSectionTensor_ne_zero s t hs ht)) =
      nonzeroMeromorphicSectionWeilDivisor X L s hs +
        nonzeroMeromorphicSectionWeilDivisor X N t ht := sorry

/-- The Weil divisor class of a tensor product of invertible modules is the sum of the classes
defined by nonzero meromorphic sections of the two factors. -/
theorem nonzeroMeromorphicSectionWeilDivisorClass_tensor
    {L N : X.Modules} [Modules.Invertible L] [Modules.Invertible N]
    (s : X.toLocallyRingedSpace.meromorphicSections L)
    (t : X.toLocallyRingedSpace.meromorphicSections N)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    (@nonzeroMeromorphicSectionWeilDivisorClass X _ _ (L ⊗ N)
        (isInvertibleObject.tensor L N)
        (X.toLocallyRingedSpace.meromorphicSectionTensor s t)
        (AlgebraicGeometry.meromorphicSectionTensor_ne_zero s t hs ht)) =
      nonzeroMeromorphicSectionWeilDivisorClass X L s hs +
        nonzeroMeromorphicSectionWeilDivisorClass X N t ht := sorry

/-- The canonical Weil divisor class associated to an invertible module. -/
noncomputable def invertibleModuleWeilDivisorClass
    (L : X.Modules) [Modules.Invertible L] : Cl(X) :=
  nonzeroMeromorphicSectionWeilDivisorClass X L
    (Modules.Invertible.regularMeromorphicSection L)
    (Modules.Invertible.regularMeromorphicSection_ne_zero L)

/-- The canonical divisor class of an invertible module can be computed from any nonzero
meromorphic section. -/
theorem invertibleModuleWeilDivisorClass_eq
    (L : X.Modules) [Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0) :
    invertibleModuleWeilDivisorClass X L =
      nonzeroMeromorphicSectionWeilDivisorClass X L s hs := sorry

/-- The canonical divisor class sends tensor products of invertible modules to sums. -/
theorem invertibleModuleWeilDivisorClass_tensor
    (L N : X.Modules) [Modules.Invertible L] [Modules.Invertible N] :
    invertibleModuleWeilDivisorClass X (L ⊗ N) =
      invertibleModuleWeilDivisorClass X L +
        invertibleModuleWeilDivisorClass X N := sorry

end AlgebraicGeometry.Scheme
