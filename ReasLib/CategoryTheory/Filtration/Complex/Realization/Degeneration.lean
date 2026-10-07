module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Dimension.Finite
public import ReasLib.CategoryTheory.Filtration.Complex.Realization
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration

@[expose] public section

open CategoryTheory
open CategoryTheory.CohomologicalSpectralSequence.Page.One
open CategoryTheory.FilteredComplex.SpectralSequence
open scoped BigOperators

noncomputable section

universe u

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

/-- For a bounded convergent realization of a cohomological spectral sequence valued
in `ModuleCat k` over a characteristic-zero field, if the first-page objects are
identified with a Hodge family vanishing outside a finite window `[0, d] × [0, d]`,
the abutment is identified with a finite-dimensional de Rham family, and in every
degree the de Rham finrank equals the sum of the Hodge finranks, then the
associated spectral sequence degenerates at page `1`. -/
theorem degeneratesAtOneOfBettiAgreement {k : Type u} [Field k] [CharZero k]
    (S : @Realization (ModuleCat k) _ _)
    (hodge : ℤ → ℤ → ModuleCat k) (deRham : ℤ → ModuleCat k) (d : ℕ)
    [∀ p q, Module.Finite k (hodge p q)] [∀ n, Module.Finite k (deRham n)]
    (pageOneIso : ∀ p q : ℤ, (S.sequence.page 1).X (p, q) ≅ hodge p q)
    (abutmentIso : ∀ n : ℤ, (S.filtered.underlying).homology n ≅ deRham n)
    (hodgeIsZero : ∀ p q : ℤ,
      p < 0 ∨ (d : ℤ) < p ∨ q < 0 ∨ (d : ℤ) < q →
        Limits.IsZero (hodge p q))
    (bettiAgreement : ∀ n : ℤ,
      Module.finrank k (deRham n) =
        ∑ p ∈ Finset.range (d + 1),
          Module.finrank k (hodge (p : ℤ) (n - (p : ℤ)))) :
    (ofZero S.sequence).degeneratesAt 1 := sorry

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
