/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Uniformity
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Ideal.LocalCohomology

/-- For an ideal of a commutative Noetherian ring and every positive `n`, some later
ideal-power quotient map `A ⧸ I ^ m ⟶ A ⧸ I ^ n` induces zero on `Tor` with every
module in every degree strictly above the local-cohomological dimension of `I`. -/
theorem exists_powerQuotientMap_torVanishesAbove_dimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : ℕ) (h : n < m),
      ∀ (N : ModuleCat.{u} A) (i : ℕ),
        dimension I I.fg_of_isNoetherianRing < (i : ℤ) →
          ((Tor (ModuleCat.{u} A) i).map
            (ModuleCat.ofHom (AdicCompletion.transitionMap I A h.le))).app N = 0 := sorry

end Ideal.LocalCohomology
