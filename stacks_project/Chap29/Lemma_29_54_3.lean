/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.Affine
import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
import ReasLib.RingTheory.IntegralClosure.Pi

open TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsReduced X]
  [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
  (U : X.affineOpens)

/- Lemma 29.54.3 (1): an affine section ring has finitely many minimal primes. -/
@[stacks 035P]
#check (Scheme.affineOpen_sections_finite_minimalPrimes U :
  (minimalPrimes Γ(X, (U : X.Opens))).Finite)

/- Lemma 29.54.3 (2): the total quotient ring is the product of the fraction
rings of the minimal-prime quotients. -/
@[stacks 035P]
#check (Localization.totalQuotientToFractionRingPi_bijective
  Γ(X, (U : X.Opens)) (Scheme.affineOpen_sections_finite_minimalPrimes U) :
    Function.Bijective
      (Localization.totalQuotientToFractionRingPi Γ(X, (U : X.Opens))))

/- Lemma 29.54.3 (3): the integral closure in the total quotient ring is the
product of the integral closures of the minimal-prime quotients. -/
@[stacks 035P]
#check (integralClosure.totalQuotientToFractionRingPi_bijective
  Γ(X, (U : X.Opens)) (Scheme.affineOpen_sections_finite_minimalPrimes U) :
    Function.Bijective
      (integralClosure.totalQuotientToFractionRingPi Γ(X, (U : X.Opens))))

/- Supporting check: finite components make the generic-point coproduct map
quasi-compact. -/
#check (GenericPointCoproduct.FiniteComponents.genericPointsQuasiCompact X :
  QuasiCompact (genericPointSpectrumCoproductTo X))

/- Supporting check: finite components make the generic-point coproduct map
quasi-separated. -/
#check (GenericPointCoproduct.FiniteComponents.genericPointsQuasiSeparated X :
  QuasiSeparated (genericPointSpectrumCoproductTo X))

/- Supporting check: sections on the generic-point coproduct over an affine
open realize the total quotient ring. -/
#check (GenericPointCoproduct.Affine.sectionsIsLocalization U :
  @IsLocalization Γ(X, (U : X.Opens)) _
    (nonZeroDivisors Γ(X, (U : X.Opens)))
    Γ(genericPointSpectrumCoproduct X,
      genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens)) _
    (GenericPointCoproduct.Affine.sectionsAlgebra U))

/- Supporting check: the inverse image of the affine open under the
normalization morphism is affine. -/
#check (IsAffineOpen.preimage U.2
  (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X)) :
    IsAffineOpen
      (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X) ⁻¹ᵁ
        (U : X.Opens)))

/- Supporting check: the normalization preimage is the range of its canonical
affine normalization chart. -/
#check (Scheme.Hom.fromNormalization_preimage
  (genericPointSpectrumCoproductTo X) U :
    Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X) ⁻¹ᵁ
        (U : X.Opens) =
      ((genericPointSpectrumCoproductTo X).normalizationOpenCover.f U).opensRange)

/- Supporting check: the section ring of the normalization preimage is the
canonical integral closure. -/
#check (Scheme.Hom.normalizationObjIso
  (genericPointSpectrumCoproductTo X) U.2 :
    Γ((genericPointSpectrumCoproductTo X).normalization,
      Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X) ⁻¹ᵁ
        (U : X.Opens)) ≅
      CommRingCat.of
        (integralClosure Γ(X, (U : X.Opens))
          Γ(genericPointSpectrumCoproduct X,
            genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens))))

/- Lemma 29.54.3 (4): the normalization preimage is the spectrum of the
integral closure in the total quotient ring. -/
@[stacks 035P]
#check (GenericPointCoproduct.Affine.TotalQuotient.normalizationPreimageIso U :
  (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X) ⁻¹ᵁ
      (U : X.Opens)).toScheme ≅
    Spec (CommRingCat.of
      (integralClosure Γ(X, (U : X.Opens))
        (Localization.totalQuotientRing Γ(X, (U : X.Opens))))))

end AlgebraicGeometry
