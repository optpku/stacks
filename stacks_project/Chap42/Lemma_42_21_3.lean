/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily.CoherentModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/- Lemma 42.21.3: for a coherent module on `X ×ₛ ℙ¹ₛ` satisfying the support
dimension bounds and the stated condition on embedded associated points, the degree-`k`
associated cycles of its zero and infinity restrictions are rationally equivalent on `X`. -/
@[stacks 02S6] #check
  (AlgebraicGeometry.ProjectiveLineFamily.fiberCycles_rationallyEquivalent :
    {S : Scheme.{u}} → [UniversallyCatenary S] → (delta : S → ℤ) →
    [IsDimensionFunction delta] → (X : Over S) → [LocallyOfFiniteType X.hom] →
    (F : (space X).Modules) → [F.IsCoherent] → (k : ℤ) →
    (h_dimension :
      (toBase X).closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport F) ≤
        ((k + 1 : ℤ) : EInt)) →
    (h_zero_dimension :
      X.hom.closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport (zeroRestriction X F)) ≤ (k : EInt)) →
    (h_infinity_dimension :
      X.hom.closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport (infinityRestriction X F)) ≤ (k : EInt)) →
    (h_embedded : ∀ ξ : space X, ξ ∈ F.embeddedAssociatedPoints →
      ξ ∉ (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support ∪
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support ∨
        (toBase X).relativeDimensionFunction delta ξ < k) →
    @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k
      (zeroAssociatedCycle delta X F k) (infinityAssociatedCycle delta X F k))

end AlgebraicGeometry.ProjectiveLineFamily
