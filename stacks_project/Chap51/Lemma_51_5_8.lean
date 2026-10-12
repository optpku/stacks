/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.SpectralSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn

noncomputable section

universe u

/- Lemma 51.5.8: for specialization-stable subsets `T, T' ⊆ Spec(A)` and
`K ∈ D⁺(A)`, the spectral sequence with second page `H_T^p(H_T'^q(K))`
finitely abuts to `H_(T ∩ T')^(p + q)(K)`. -/
@[stacks 0EF6] #check (CategoryTheory.ModuleCat.SupportedOn.existsSpectralSequence :
  ∀ {A : Type u} [CommRing A] (T T' : Set (PrimeSpectrum A)),
    StableUnderSpecialization T → StableUnderSpecialization T' →
    ∀ K : DerivedCategory.Plus (ModuleCat.{u} A),
      ∃ E : E₂CohomologicalSpectralSequence (ModuleCat.{u} A),
        (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 2).X (Int.ofNat p, q) ≅
          ((sectionsWithSupport T).rightDerived p).obj (cohomologyPlus T' K q))) ∧
        (∀ p q : ℤ, p < 0 → IsZero ((E.page 2).X (p, q))) ∧
        (∃ lowerBound : ℤ, ∀ p q : ℤ, q < lowerBound → IsZero ((E.page 2).X (p, q))) ∧
        E.FinitelyAbutsTo (fun degree ↦ cohomologyPlus (T ∩ T') K degree))
