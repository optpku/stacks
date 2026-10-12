/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.DerivedFinitenessCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat.SupportedOn
open DerivedCategory.Plus.CohomologyIn
open CategoryTheory.DerivedCategory.LocalizationAtPrime
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

/- Proposition 51.14.2: for a Noetherian ring with a dualizing complex, a
specialization-stable subset `T` of the spectrum, an integer `s`, and a bounded-below
coherent derived complex `K`, supported cohomology is finite through degree `s` exactly
when every chain `p ⊆ q`, with `p ∉ T` and `q ∈ T`, satisfies
`s < depth_{A_p}(K_p) + dim((A/p)_q)`. -/
@[stacks 0EI2]
#check
  (@CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_derivedDepth_add_quotientDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (s : ℤ)
    (K : D⁺[ModuleCat.isFinitePresentation A])
    (RΓ : ∀ p : PrimeSpectrum A,
      DerivedCategory (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) ⥤
        DerivedCategory.IdealPowerTorsion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))
    (hRΓ : ∀ p : PrimeSpectrum A,
      DerivedCategory.IdealPowerTorsion.inclusion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ⊣ RΓ p),
    (∀ i : ℤ, i ≤ s →
      Module.Finite A
        (cohomology T ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
          (s : EInt) <
            ((DerivedCategory.depth (RΓ p) (hRΓ p)
                ((coherent p).obj K) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (p.asIdeal.quotientAtPrime q)))
