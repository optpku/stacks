/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

open scoped ENat

universe u

namespace IsNormalRing

/-- For a complete Noetherian normal local ring of dimension at least four and a nonzero
maximal-ideal element `f`, the depth of the localized quotient by `f` plus the dimension
of the prime quotient is strictly greater than one on the punctured vanishing locus of `f`. -/
theorem one_lt_depth_quotient_add_dim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsCompleteLocalRing A] [IsNormalRing A]
    (h_dim : 4 ≤ ringKrullDim A) (f : A)
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A) (h_f_ne : f ≠ 0) :
    ∀ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
        p ≠ IsLocalRing.closedPoint A →
          (.some (1 : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal
                (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
              WithBot ℕ∞) +
              ringKrullDim (A ⧸ p.asIdeal) := sorry

/-- For a complete Noetherian normal local ring of dimension at least four and a nonzero
maximal-ideal element `f`, the depth at a prime plus the dimension of its quotient is
strictly greater than three outside the vanishing locus of `f` whenever the prime's
vanishing locus meets that of `f` in more than the closed point. -/
theorem three_lt_depth_add_dim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsCompleteLocalRing A] [IsNormalRing A]
    (h_dim : 4 ≤ ringKrullDim A) (f : A)
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A) (h_f_ne : f ≠ 0) :
    ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
          {IsLocalRing.closedPoint A} →
          (.some (3 : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
              ringKrullDim (A ⧸ p.asIdeal) := sorry

end IsNormalRing
