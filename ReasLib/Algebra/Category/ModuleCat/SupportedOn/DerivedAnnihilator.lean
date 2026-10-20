module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Depth
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.CoherentLocalization
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

open CategoryTheory
open DerivedCategory.Plus
open CategoryTheory.DerivedCategory.LocalizationAtPrime
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

open CohomologyIn in
/-- For a bounded-below complex with coherent cohomology over a Noetherian ring admitting
a dualizing complex, one ideal supported in `T'` annihilates its `T`-supported local
cohomology through degree `s` if and only if every chain `p ⊆ q`, with `p ∉ T'` and
`q ∈ T`, satisfies `s < depth(K_p) + dim((A/p)_q)`. -/
theorem existsAnnihilator_iff_derivedDepth_add_quotientDim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizing)
    (T T' : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (hTT' : T ⊆ T') (s : ℤ)
    (K : D⁺[ModuleCat.isFinitePresentation A])
    (RΓ : ∀ p : PrimeSpectrum A,
      DerivedCategory (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) ⥤
        DerivedCategory.IdealPowerTorsion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))
    (hRΓ : ∀ p : PrimeSpectrum A,
      DerivedCategory.IdealPowerTorsion.inclusion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ⊣ RΓ p) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s →
        J ≤ Module.annihilator A
          (cohomology T
            ((ambient (ModuleCat.isFinitePresentation A)).obj K) i)) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
          (s : EInt) <
            ((DerivedCategory.depth (RΓ p) (hRΓ p)
                ((coherent p).obj K) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (p.asIdeal.quotientAtPrime q)) := sorry

end CategoryTheory.ModuleCat.SupportedOn
