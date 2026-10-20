module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered spectral sequences for derived completion

A filtered cochain complex and a finitely generated ideal determine a cohomological spectral
sequence whose first page is computed by derived completions of the graded pieces.  This file
bundles the spectral sequence, its filtered realization, and the two canonical comparison
isomorphisms so that downstream consumers do not have to unpack a nested existential.

@stack 0BKD
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory.DerivedCompletion

variable {A : Type u} [CommRing A]
variable [LocallySmall.{0} (ModuleCat A)] [WellPowered.{0} (ModuleCat A)]

/-- The filtered derived-completion spectral sequence attached to `K`. -/
@[stacks 0BKD "filtered derived-completion spectral sequence"]
structure FilteredSpectralSequence (I : Ideal A)
    (K : FilteredCochainComplex (ModuleCat A)) where
  /-- A reflector realizing derived completion with respect to `I`. -/
  completion : Reflector I
  /-- The cohomological spectral sequence associated to the filtered realization. -/
  spectralSequence : CohomologicalSpectralSequence (ModuleCat A) 0
  /-- A filtered complex representing the derived completion of the input filtered complex. -/
  filteredComplex : FilteredComplex (ModuleCat A)
  /-- The filtered complex is associated to the chosen spectral sequence. -/
  associated : FilteredComplex.IsAssociated filteredComplex spectralSequence
  /-- The first page is the cohomology of the completed graded pieces. -/
  pageOneIso (p q : ℤ) :
    (spectralSequence.page 1).X (p, q) ≅
      completion.cohomology (p + q) (Q.obj (K.gradedPiece p))
  /-- The filtered realization computes the cohomology of the completed underlying complex. -/
  targetIso (n : ℤ) :
    filteredComplex.underlying.homology n ≅
      completion.cohomology n (Q.obj K.underlying)
  /-- Every page from `E₁` onward consists of derived-complete modules. -/
  pageIsDerivedComplete (r : ℕ) (hr : 1 ≤ r) (p q : ℤ) :
    ((spectralSequence.page r).X (p, q)).IsDerivedCompleteWithRespectTo I
  /-- Finite term filtrations make the spectral sequence bounded. -/
  boundedOfFiniteFiltrations : K.HasFiniteFiltrations → spectralSequence.IsBounded
  /-- Finite term filtrations make the filtered realization converge. -/
  convergesOfFiniteFiltrations : K.HasFiniteFiltrations →
    FilteredComplex.Cohomology.Convergence.Converges filteredComplex spectralSequence

namespace FilteredSpectralSequence

/-- The abutment of a filtered completion spectral sequence is canonically isomorphic to
cohomology of the supplied derived completion of the underlying complex. -/
noncomputable def canonicalTargetIso {I : Ideal A}
    {K : FilteredCochainComplex (ModuleCat A)}
    (S : FilteredSpectralSequence I K) (R : Reflector I) (n : ℤ) :
    S.filteredComplex.underlying.homology n ≅
      (homologyFunctor (ModuleCat A) n).obj
        (R.obj (Q.obj K.underlying)) :=
  S.targetIso n ≪≫
    (homologyFunctor (ModuleCat A) n).mapIso
      ((S.completion.completionIso R).app (Q.obj K.underlying))

/-- The bundled proof specification of a filtered derived-completion spectral sequence. -/
@[stacks 0BKD "filtered derived-completion spectral sequence specification"]
theorem spec {I : Ideal A} {K : FilteredCochainComplex (ModuleCat A)}
    (S : FilteredSpectralSequence I K) :
    FilteredComplex.IsAssociated S.filteredComplex S.spectralSequence ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ p q : ℤ,
        ((S.spectralSequence.page r).X (p, q)).IsDerivedCompleteWithRespectTo I) ∧
      (K.HasFiniteFiltrations →
        S.spectralSequence.IsBounded ∧
          FilteredComplex.Cohomology.Convergence.Converges
            S.filteredComplex S.spectralSequence) := sorry

end FilteredSpectralSequence

/-- A filtered cochain complex admits a filtered
derived-completion spectral sequence for every finitely generated ideal. -/
@[stacks 0BKD]
theorem existsFilteredSpectralSequence
    (I : Ideal A) (hI : I.FG) (K : FilteredCochainComplex (ModuleCat A)) :
    Nonempty (FilteredSpectralSequence I K) := sorry

end DerivedCategory.DerivedCompletion
