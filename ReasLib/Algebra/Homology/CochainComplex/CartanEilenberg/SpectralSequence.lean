module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.TotalFunctoriality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.SpectralSequence
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence

/-!
# Spectral Sequences of Mapped Cartan--Eilenberg Resolutions

This leaf specializes the two standard filtered-total spectral sequences to the termwise image
of a Cartan--Eilenberg resolution.  It removes finite-support bookkeeping from downstream calls
while leaving page identifications and derived-functor comparisons in their finer owner modules.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K : CochainComplex.Plus A} (I : CartanEilenbergResolution K)
variable (F : A ⥤ B) [F.Additive]

namespace SpectralSequence.First

/-- The first standard filtration on a mapped Cartan--Eilenberg total is finite in every
degree. -/
@[stacks 015J "finite first filtration of a mapped Cartan-Eilenberg total"]
theorem hasFiniteFiltrations :
    (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)).HasFiniteFiltrations := sorry

/-- A spectral sequence associated to the first standard filtration of a mapped
Cartan--Eilenberg resolution is bounded. -/
@[stacks 015J "boundedness of the first Cartan-Eilenberg spectral sequence"]
theorem associated_isBounded
    {E : CohomologicalSpectralSequence B 0}
    (hAssoc : FilteredComplex.IsAssociated
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E) :
    E.IsBounded := sorry

end SpectralSequence.First

namespace SpectralSequence.Second

/-- The second standard filtration on a mapped Cartan--Eilenberg total is finite in every
degree. -/
@[stacks 015J "finite second filtration of a mapped Cartan-Eilenberg total"]
theorem hasFiniteFiltrations :
    (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)).HasFiniteFiltrations := sorry

/-- A spectral sequence associated to the second standard filtration of a mapped
Cartan--Eilenberg resolution is bounded. -/
@[stacks 015J "boundedness of the second Cartan-Eilenberg spectral sequence"]
theorem associated_isBounded
    {E : CohomologicalSpectralSequence B 0}
    (hAssoc : FilteredComplex.IsAssociated
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E) :
    E.IsBounded := sorry

end SpectralSequence.Second

namespace SpectralSequence.First

/-- The first standard filtration on the cohomology of a mapped Cartan--Eilenberg total is
finite in every degree. -/
@[stacks 015J "finiteness of the first Cartan-Eilenberg abutment filtration"]
theorem Cohomology.isFinite :
    FilteredComplex.Cohomology.Filtration.IsFinite
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) := sorry

end SpectralSequence.First

namespace SpectralSequence.Second

/-- The second standard filtration on the cohomology of a mapped Cartan--Eilenberg total is
finite in every degree. -/
@[stacks 015J "finiteness of the second Cartan-Eilenberg abutment filtration"]
theorem Cohomology.isFinite :
    FilteredComplex.Cohomology.Filtration.IsFinite
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) := sorry

end SpectralSequence.Second

namespace SpectralSequence.First

/-- The first standard spectral sequence of a mapped Cartan--Eilenberg resolution converges to
the cohomology of its total complex. -/
@[stacks 015J "convergence of the first Cartan-Eilenberg spectral sequence"]
theorem converges
    {E : CohomologicalSpectralSequence B 0}
    (hAssoc : FilteredComplex.IsAssociated
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E) :
    FilteredComplex.Cohomology.Convergence.Converges
      (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)) E := sorry

end SpectralSequence.First

namespace SpectralSequence.Second

/-- The second standard spectral sequence of a mapped Cartan--Eilenberg resolution converges to
the cohomology of its total complex. -/
@[stacks 015J "convergence of the second Cartan-Eilenberg spectral sequence"]
theorem converges
    {E : CohomologicalSpectralSequence B 0}
    (hAssoc : FilteredComplex.IsAssociated
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E) :
    FilteredComplex.Cohomology.Convergence.Converges
      (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)) E := sorry

end SpectralSequence.Second

end CochainComplex.CartanEilenbergResolution
