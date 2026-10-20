module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing.MeromorphicSection

/-!
# Orders of tensor products of meromorphic sections

The order of a tensor product of regular meromorphic sections of invertible modules is the sum
of their orders along each prime divisor.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

/-- Along a prime divisor, the order of the tensor product of two regular meromorphic sections
of invertible modules is the sum of their orders. -/
theorem regularMeromorphicSectionOrderAlongPrimeDivisor_tensor
    {L N : X.Modules} [Modules.Invertible L] [Modules.Invertible N]
    (s : X.toLocallyRingedSpace.meromorphicSections L)
    (t : X.toLocallyRingedSpace.meromorphicSections N)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection L s)
    (ht : X.toLocallyRingedSpace.IsRegularMeromorphicSection N t)
    (Z : PrimeDivisor X) :
    (@regularMeromorphicSectionOrderAlongPrimeDivisor X _ _ (L ⊗ N)
        (CategoryTheory.MonoidalCategory.isInvertibleObject.tensor L N)
        (X.toLocallyRingedSpace.meromorphicSectionTensor s t)
        (@LocallyRingedSpace.isRegularMeromorphicSection_tensor
          X.toLocallyRingedSpace L N
          (Modules.Invertible.ringedSpaceIsInvertible
            (inferInstance : Modules.Invertible L))
          (Modules.Invertible.ringedSpaceIsInvertible
            (inferInstance : Modules.Invertible N)) s t hs ht) Z) =
      regularMeromorphicSectionOrderAlongPrimeDivisor s hs Z +
        regularMeromorphicSectionOrderAlongPrimeDivisor t ht Z := sorry

end AlgebraicGeometry.Scheme
