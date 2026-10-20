module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.FinitePresentation

/-!
# The DVR-valuative criterion over locally Noetherian schemes

For finite-type morphisms to locally Noetherian schemes, universal closedness can be tested
using either relative affine spaces, arbitrary valuation rings, or discrete valuation rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ValuativeCriterion.DVR

/-- For a finite-type morphism to a locally Noetherian scheme, universal closedness is equivalent
to closedness after every finite-dimensional relative affine-space base change, existence in the
valuative criterion, and existence in the DVR-valuative criterion. -/
theorem universallyClosed_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [IsLocallyNoetherian S] :
    List.TFAE
      [ UniversallyClosed f
      , ∀ n : ℕ,
          IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base
      , ValuativeCriterion.Existence f
      , ValuativeCriterion.DVR.Existence f
      ] := sorry

end AlgebraicGeometry.ValuativeCriterion.DVR
