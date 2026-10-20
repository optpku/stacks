/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.FrobeniusColimit
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 38.39.3: for a prime `p`, restriction from the canonical two-generator almost blowup
square in characteristic `p` induces an equivalence from the Frobenius colimit of vector bundles
on the base to the categorical pullback of the corresponding colimits on the other vertices. -/
@[stacks 0EXD] #check (
  AlgebraicGeometry.TwoGeneratorProj.FrobeniusColimit.comparisonIsEquivalence :
    ∀ (p : ℕ) [Fact p.Prime] (A : CommRingCat.{u}) [CharP A p] (f₁ f₂ : A),
      (AlgebraicGeometry.TwoGeneratorProj.FrobeniusColimit.comparison p A f₁ f₂).IsEquivalence)
