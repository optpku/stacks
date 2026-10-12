/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily.AssociatedCycle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/- Lemma 42.21.2: if a closed subscheme `Z` of `X ×ₛ ℙ¹ₛ` has
`delta`-dimension at most `k + 1`, its endpoint fibers have `delta`-dimension at most
`k`, and every embedded point of `Z` is either outside both endpoint fibers or has
`delta`-dimension less than `k`, then its zero and infinity endpoint `k`-cycles are
rationally equivalent on `X`. -/
@[stacks 02S5] #check
  (AlgebraicGeometry.ProjectiveLineFamily.zeroCycle_rationallyEquivalent_infinityCycle_of_dimension_le :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
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
            delta (Z.subschemeι ξ) < k),
      @RationalEquivalence.RationallyEquivalent X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance k
        (zeroCycle delta X k Z) (infinityCycle delta X k Z))

end AlgebraicGeometry.ProjectiveLineFamily
