/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup.FrobeniusColimit
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 38.39.2: for the characteristic-`p` principal-center almost blowup square of
Example 38.37.10, the canonical comparison from the Frobenius colimit of vector bundles on
the base to the categorical pullback of the colimits on the other three vertices is an
equivalence. -/
@[stacks 0EXC] #check
  (AlgebraicGeometry.Spec.PrincipalCenter.FrobeniusColimit.comparisonIsEquivalence :
    ∀ (p : ℕ) [Fact p.Prime]
      (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
      (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0),
      (AlgebraicGeometry.Spec.PrincipalCenter.FrobeniusColimit.comparison
        p A f J hJfg hJ).IsEquivalence)
