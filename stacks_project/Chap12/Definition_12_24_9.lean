/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)

/- Definition 12.24.9 (1) [012U]: weak convergence compares the induced cohomology filtration
with the infinity page of the chosen spectral sequence. -/
@[stacks 012U]
#check (FilteredComplex.Cohomology.Convergence.IsWeak K E : Prop)
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.isAssociated
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.isIsomorphic
#check @FilteredComplex.Cohomology.Convergence.IsWeak.of_along
#check @FilteredComplex.Cohomology.Convergence.IsWeak.exists_along
#check @FilteredComplex.Cohomology.Convergence.IsWeak.isAssociated

/- Definition 12.24.9 (2) [012U]: abutment adds separatedness and exhaustiveness of the induced
cohomology filtration. -/
@[stacks 012U]
#check (FilteredComplex.Cohomology.Convergence.Abuts K E : Prop)
#check @FilteredComplex.Cohomology.Convergence.AbutsAlong
#check @FilteredComplex.Cohomology.Convergence.AbutsAlong.isWeak
#check @FilteredComplex.Cohomology.Convergence.AbutsAlong.isSeparatedExhaustive
#check @FilteredComplex.Cohomology.Convergence.AbutsAlong.of_isWeak
#check @FilteredComplex.Cohomology.Convergence.Abuts.isWeak
#check @FilteredComplex.Cohomology.Convergence.Abuts.isSeparatedExhaustive
#check @FilteredComplex.Cohomology.Convergence.Abuts.exists_along

/- Definition 12.24.9 (3) [012U]: convergence adds regularity and completeness. -/
@[stacks 012U]
#check (FilteredComplex.Cohomology.Convergence.Converges K E : Prop)
#check @FilteredComplex.Cohomology.Convergence.ConvergesAlong
#check @FilteredComplex.Cohomology.Convergence.ConvergesAlong.isRegular
#check @FilteredComplex.Cohomology.Convergence.ConvergesAlong.abuts
#check @FilteredComplex.Cohomology.Convergence.ConvergesAlong.isComplete
#check @FilteredComplex.Cohomology.Convergence.ConvergesAlong.of_abuts
#check @FilteredComplex.Cohomology.Convergence.Converges.isRegular
#check @FilteredComplex.Cohomology.Convergence.Converges.abuts
#check @FilteredComplex.Cohomology.Convergence.Converges.isComplete
#check @FilteredComplex.Cohomology.Convergence.Converges.exists_along

/- The completeness component is canonically owned by the quotient tower of a decreasing
filtration. -/
#check @DecreasingFiltration.IsComplete

/- Completeness of all induced cohomology filtrations. -/
#check @FilteredComplex.Cohomology.Filtration.IsComplete
