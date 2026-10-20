module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints

/-!
# Effective Cartier divisor approximations without embedded points

An effective Cartier divisor approximation of a codimension-one closed subscheme without
embedded points identifies that subscheme as an effective Cartier divisor.
-/

@[expose] public section

open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

namespace EffectiveCartierDivisorApproximation

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A closed subscheme without embedded points that admits an effective Cartier divisor
approximation is an effective Cartier divisor when every generic point has ambient stalk
dimension one. -/
theorem isEffectiveCartierDivisor_of_noEmbeddedPoints_of_codimensionOne
    (Z D : X.IdealSheafData) (h_approx : EffectiveCartierDivisorApproximation D Z)
    (h_embedded : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (h_codim :
      ∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
        ringKrullDim (X.presheaf.stalk (Z.subschemeι.base ξ)) = 1) :
    AlgebraicGeometry.IsEffectiveCartierDivisor Z.subschemeι := sorry

end EffectiveCartierDivisorApproximation

namespace NoEmbeddedPoints

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A codimension-one closed subscheme without embedded points is an effective Cartier divisor
if all ambient stalks along its support are unique factorization monoids or the ambient scheme
is regular. -/
theorem isEffectiveCartierDivisor_of_stalks_uniqueFactorizationMonoid_or_regular
    (Z : X.IdealSheafData)
    (h_embedded : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (h_codim :
      ∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
        ringKrullDim (X.presheaf.stalk (Z.subschemeι.base ξ)) = 1)
    (h_UFD_or_regular :
      (∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨
        AlgebraicGeometry.Scheme.Regular X) :
    AlgebraicGeometry.IsEffectiveCartierDivisor Z.subschemeι := sorry

end NoEmbeddedPoints

end AlgebraicGeometry.Scheme.IdealSheafData
