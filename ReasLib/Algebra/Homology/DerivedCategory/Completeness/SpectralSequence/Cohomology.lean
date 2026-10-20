module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Filtered
import Mathlib.Tactic.CrossRefAttribute

/-!
# The cohomology spectral sequence for derived completion

Applying the filtered derived-completion construction to the canonical truncation filtration gives
a bounded spectral sequence whose second page is the cohomology of the completed cohomology
modules and whose abutment is the cohomology of the derived completion.

@stack 0BKE
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory.DerivedCompletion

variable {A : Type u} [CommRing A]
variable [LocallySmall.{0} (ModuleCat A)] [WellPowered.{0} (ModuleCat A)]

/-- The bounded cohomology spectral sequence for the derived completion of `K`. -/
@[stacks 0BKE "derived-completion cohomology spectral sequence"]
structure CohomologySpectralSequence (I : Ideal A)
    (K : DerivedCategory (ModuleCat A)) where
  /-- A reflector realizing derived completion with respect to `I`. -/
  completion : Reflector I
  /-- The cohomological spectral sequence beginning at the renumbered second page. -/
  spectralSequence : CohomologicalSpectralSequence (ModuleCat A) 0
  /-- A filtered complex realizing the abutment. -/
  filteredComplex : FilteredComplex (ModuleCat A)
  /-- The filtered realization is associated to the chosen spectral sequence. -/
  associated : FilteredComplex.IsAssociated filteredComplex spectralSequence
  /-- The spectral sequence is bounded. -/
  bounded : spectralSequence.IsBounded
  /-- Its second page is cohomology of the completed cohomology modules of `K`. -/
  pageTwoIso (i j : ℤ) :
    (spectralSequence.page 2).X (i, j) ≅
      completion.cohomology i
        ((singleFunctor (ModuleCat A) (0 : ℤ)).obj
          ((homologyFunctor (ModuleCat A) j).obj K))
  /-- Every page from `E₂` onward consists of derived-complete modules. -/
  pageIsDerivedComplete (r : ℕ) (hr : 2 ≤ r) (i j : ℤ) :
    ((spectralSequence.page r).X (i, j)).IsDerivedCompleteWithRespectTo I
  /-- The filtered realization converges to the spectral-sequence abutment. -/
  converges :
    FilteredComplex.Cohomology.Convergence.Converges filteredComplex spectralSequence
  /-- The abutment is the cohomology of the derived completion of `K`. -/
  targetIso (n : ℤ) :
    filteredComplex.underlying.homology n ≅ completion.cohomology n K

namespace CohomologySpectralSequence

/-- The bundled proof specification of the derived-completion cohomology spectral sequence. -/
@[stacks 0BKE "derived-completion cohomology spectral sequence specification"]
theorem spec {I : Ideal A} {K : DerivedCategory (ModuleCat A)}
    (S : CohomologySpectralSequence I K) :
    S.spectralSequence.IsBounded ∧
      (∀ (r : ℕ), 2 ≤ r → ∀ i j : ℤ,
        ((S.spectralSequence.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
      FilteredComplex.IsAssociated S.filteredComplex S.spectralSequence ∧
      FilteredComplex.Cohomology.Convergence.Converges
        S.filteredComplex S.spectralSequence := sorry

/-- The abutment of a completion cohomology spectral sequence is canonically isomorphic to
cohomology of the supplied derived completion. -/
noncomputable def canonicalTargetIso {I : Ideal A} {K : DerivedCategory (ModuleCat A)}
    (S : CohomologySpectralSequence I K) (R : Reflector I) (n : ℤ) :
    S.filteredComplex.underlying.homology n ≅
      (homologyFunctor (ModuleCat A) n).obj (R.obj K) :=
  S.targetIso n ≪≫
    (homologyFunctor (ModuleCat A) n).mapIso
      ((S.completion.completionIso R).app K)

end CohomologySpectralSequence

/-- For a finitely generated ideal and a derived module, there is a bounded spectral sequence
whose second page consists of cohomology of the completed cohomology modules and whose
abutment is cohomology of the derived completion. -/
@[stacks 0BKE]
theorem existsCohomologySpectralSequence
    (I : Ideal A) (hI : I.FG) (K : DerivedCategory (ModuleCat A)) :
    Nonempty (CohomologySpectralSequence I K) := sorry

end DerivedCategory.DerivedCompletion
