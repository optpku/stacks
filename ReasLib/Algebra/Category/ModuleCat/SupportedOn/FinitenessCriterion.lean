/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Finiteness
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Annihilator

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/-- For a finite module over a Noetherian ring admitting a dualizing complex,
cohomology supported on a specialization-stable subset `T` is finite through
degree `s` exactly when the localized depth-plus-quotient-dimension inequality
holds along every prime chain from outside `T` into `T`. -/
theorem cohomology_finite_iff_depth_add_quotientDim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (s : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (∀ i : ℕ, i ≤ s →
      Module.Finite A
        (cohomology T (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
          (.some (s : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
                ringKrullDim (p.asIdeal.quotientAtPrime q) := sorry

end CategoryTheory.ModuleCat.SupportedOn
