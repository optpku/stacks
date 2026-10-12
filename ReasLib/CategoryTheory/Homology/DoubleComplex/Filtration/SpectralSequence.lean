/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence

/-!
# Spectral Sequences of a Double Complex

This leaf supplies the joint existence interface for the spectral sequences associated to the
two standard filtrations of a cohomological double complex.  Page computations, boundedness, and
convergence remain in their finer-grained owner modules.

@stack 0130
-/

@[expose] public section

open CategoryTheory ComplexShape

universe v u

namespace HomologicalComplex₂

namespace Filtration

namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The two standard filtrations of a cohomological double complex admit associated
cohomological spectral sequences. -/
@[stacks 0130 "the two spectral sequences of a double complex"]
theorem existsPair
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    ∃ E₁ E₂ : CohomologicalSpectralSequence C 0,
      FilteredComplex.IsAssociated (First.Filtration.total K) E₁ ∧
        FilteredComplex.IsAssociated (Second.Filtration.total K) E₂ := sorry

end SpectralSequence

end Filtration

end HomologicalComplex₂
