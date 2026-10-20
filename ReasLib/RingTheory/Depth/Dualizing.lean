/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace SerreConditionS

/-- In a Noetherian local ring with a dualizing complex, depth at least three,
Serre's condition `(S₂)`, and dimension at least four, every prime containing a
regular maximal-ideal element and having two-dimensional quotient has localized
depth at least two. -/
theorem primeDepth_ge_two_of_dualizing_dimension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    [SerreConditionS A 2]
    (h_dim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal) := sorry

end SerreConditionS
