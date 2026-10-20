module

import ReasLib.CategoryTheory.Filtration.Complex.Realization.Degeneration
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.CohomologicalSpectralSequence.Page.One
open CategoryTheory.FilteredComplex.SpectralSequence
open scoped BigOperators

universe u

/- Remark 50.22.2: if Betti numbers of a bounded convergent Hodge-to-de Rham
realization over a characteristic-zero field agree with the Hodge-number sums,
the spectral sequence degenerates at `E₁`. -/
@[stacks 0FWE] #check (CategoryTheory.FilteredComplex.SpectralSequence.Realization.degeneratesAtOneOfBettiAgreement :
    {k : Type u} → [Field k] → [CharZero k] →
    (S : @Realization (ModuleCat k) _ _) →
    (hodge : ℤ → ℤ → ModuleCat k) → (deRham : ℤ → ModuleCat k) → (d : ℕ) →
    [∀ p q, Module.Finite k (hodge p q)] → [∀ n, Module.Finite k (deRham n)] →
    (pageOneIso : ∀ p q : ℤ, (S.sequence.page 1).X (p, q) ≅ hodge p q) →
    (abutmentIso : ∀ n : ℤ, (S.filtered.underlying).homology n ≅ deRham n) →
    (hodgeIsZero : ∀ p q : ℤ,
      p < 0 ∨ (d : ℤ) < p ∨ q < 0 ∨ (d : ℤ) < q →
        Limits.IsZero (hodge p q)) →
    (bettiAgreement : ∀ n : ℤ,
      Module.finrank k (deRham n) =
        ∑ p ∈ Finset.range (d + 1),
          Module.finrank k (hodge (p : ℤ) (n - (p : ℤ)))) →
    (ofZero S.sequence).degeneratesAt 1)
