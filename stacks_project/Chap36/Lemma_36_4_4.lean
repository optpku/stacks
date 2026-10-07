module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections.Filtered.Truncation
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence
open CategoryTheory.FilteredComplex.Cohomology.Convergence

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.4.4 (1): for a quasi-compact and quasi-separated scheme, the truncation
hypercohomology spectral sequence of an object of `D_QCoh(𝒪_X)` is bounded. -/
@[stacks 0G9Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.truncationSpectralSequence_isBounded :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : DerivedQCoh X)
      (S : Truncation.Realization X.toRingedSpace ((inclusion X).obj K)),
      S.sequence.IsBounded)

/- Lemma 36.4.4 (2): for a quasi-compact and quasi-separated scheme, the truncation
hypercohomology spectral sequence of an object of `D_QCoh(𝒪_X)` converges to its
hypercohomology. -/
@[stacks 0G9Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.truncationSpectralSequence_converges :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : DerivedQCoh X)
      (S : Truncation.Realization X.toRingedSpace ((inclusion X).obj K)),
      ConvergesViaRenumbering S.filtered S.originalSequence S.sequence)

end AlgebraicGeometry.Scheme.DerivedQCoh
