/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered.Truncation
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologicalDimension
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Convergence

/-!
# Truncation hypercohomology spectral sequences on schemes

This file records boundedness and convergence of the truncation hypercohomology spectral
sequence for derived modules with quasi-coherent cohomology on quasi-compact,
quasi-separated schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence
open CategoryTheory.FilteredComplex.Cohomology.Convergence

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a quasi-compact, quasi-separated scheme, the truncation hypercohomology spectral
sequence of a derived module with quasi-coherent cohomology is bounded. -/
theorem truncationSpectralSequence_isBounded {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (K : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (S : Truncation.Realization X.toRingedSpace K.obj) :
    S.sequence.IsBounded := sorry

/-- On a quasi-compact, quasi-separated scheme, the truncation hypercohomology spectral
sequence of a derived module with quasi-coherent cohomology converges to its
hypercohomology. -/
theorem truncationSpectralSequence_converges {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (K : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (S : Truncation.Realization X.toRingedSpace K.obj) :
    ConvergesViaRenumbering S.filtered S.originalSequence S.sequence := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
