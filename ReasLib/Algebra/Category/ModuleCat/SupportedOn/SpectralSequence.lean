module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FiniteAbutment
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

open Limits

variable {A : Type u} [CommRing A]

/-- Successive cohomology with specialization-stable supports admits a bounded spectral
sequence with second page `H_T^p(H_T'^q(K))`, finitely abutting to cohomology supported on
`T ∩ T'` for every bounded-below derived module `K`. -/
theorem existsSpectralSequence (T T' : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) :
    ∃ E : E₂CohomologicalSpectralSequence (ModuleCat.{u} A),
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 2).X (Int.ofNat p, q) ≅
        ((sectionsWithSupport T).rightDerived p).obj (cohomologyPlus T' K q))) ∧
      (∀ p q : ℤ, p < 0 → IsZero ((E.page 2).X (p, q))) ∧
      (∃ lowerBound : ℤ, ∀ p q : ℤ, q < lowerBound → IsZero ((E.page 2).X (p, q))) ∧
      E.FinitelyAbutsTo (fun degree ↦ cohomologyPlus (T ∩ T') K degree) := sorry

end CategoryTheory.ModuleCat.SupportedOn
