/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Annihilator
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

/- Proposition 51.10.1 (0EFC): for a finite module over a Noetherian ring admitting a
dualizing complex, a single ideal supported in `T'` annihilates its local cohomology
with support in `T` through degree `s` exactly when the corresponding localized
depth-plus-dimension inequality holds along every chain `p ⊆ q` with `p ∉ T'` and
`q ∈ T`. -/
@[stacks 0EFC]
#check
  (@CategoryTheory.ModuleCat.SupportedOn.exists_annihilator_localCohomology_iff_depth_add_quotientDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
      (T T' : Set (PrimeSpectrum A))
      (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
      (hTT' : T ⊆ T') (s : ℕ)
      (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ i : ℕ, i ≤ s →
          J ≤ Module.annihilator A
            (ModuleCat.SupportedOn.cohomology T
              (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
        ∀ p q : PrimeSpectrum A,
          p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
            (.some (s : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
                  ringKrullDim (p.asIdeal.quotientAtPrime q))
