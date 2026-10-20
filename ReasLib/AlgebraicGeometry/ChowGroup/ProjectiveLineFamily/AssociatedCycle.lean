module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The zero and infinity endpoint cycles of a closed subscheme of a projective-line family
are rationally equivalent when its total space and endpoint fibers satisfy the prescribed
dimension bounds and its embedded points at the endpoints have smaller dimension. -/
theorem zeroCycle_rationallyEquivalent_infinityCycle_of_dimension_le
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    (Z : (space X).IdealSheafData)
    (h_dimension :
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).closedSubschemeDeltaDimension
        delta Z ≤ ((k + 1 : ℤ) : EInt))
    (h_zero_dimension :
      X.hom.closedSubschemeDeltaDimension delta (zeroImage X Z) ≤ (k : EInt))
    (h_infinity_dimension :
      X.hom.closedSubschemeDeltaDimension delta (infinityImage X Z) ≤ (k : EInt))
    (h_embedded : ∀ ξ : Z.subscheme, Z.subscheme.embeddedPoint ξ →
      ξ ∉ ((zeroDivisor X Z).support : Set Z.subscheme) ∪
          ((infinityDivisor X Z).support : Set Z.subscheme) ∨
        (pullback.fst X.hom (ProjectiveSpace.toBase 1 S) ≫ X.hom).relativeDimensionFunction
          delta (Z.subschemeι ξ) < k) :
    @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k
      (zeroCycle delta X k Z) (infinityCycle delta X k Z) := sorry

end AlgebraicGeometry.ProjectiveLineFamily
