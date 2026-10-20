/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.TwoPeriodic

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory

universe u

/- Lemma 42.69.2: If a coherent two-periodic complex has support of relative
`δ`-dimension at most `k + 1`, and each of its two homology sheaves has support of
relative `δ`-dimension at most `k`, then their degree-`k` associated cycles are
rationally equivalent. -/
@[stacks 02SB] #check
  (CategoryTheory.TwoPeriodicEndomorphism.homologyCycles_rationallyEquivalent :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (K : TwoPeriodicEndomorphism X.Modules) [K.X.IsCoherent] (k : ℤ)
      (hF : p.closedSubschemeDeltaDimension δ
        (schemeTheoreticSupport K.X) ≤ ((k + 1 : ℤ) : EInt))
      (hH0 : p.closedSubschemeDeltaDimension δ
        (schemeTheoreticSupport (K.toCochainComplex.homology 0)) ≤ (k : EInt))
      (hH1 : p.closedSubschemeDeltaDimension δ
        (schemeTheoreticSupport (K.toCochainComplex.homology 1)) ≤ (k : EInt)),
      @RationalEquivalence.RationallyEquivalent X
        (LocallyOfFiniteType.isLocallyNoetherian p) (p.relativeDimensionFunction δ)
        inferInstance k (K.relativeHomologyCycle p δ 0 k)
        (K.relativeHomologyCycle p δ 1 k))
