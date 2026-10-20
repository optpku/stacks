module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)

/- Definition 12.24.9 (1) [012U]: weak convergence asks that the subquotient identification of
`gr^p H^n(K)` inside `E_∞^{p,n-p}` from Lemma 12.24.8 be an equality, i.e. that the eventual
representatives `Z_∞`, `B_∞` agree with the intrinsic cycles and boundaries. -/
@[stacks 012U]
#check (FilteredComplex.Cohomology.Convergence.IsWeak K E : Prop)
#check @FilteredComplex.Cohomology.Convergence.LimitRepresentatives
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.isAssociated
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.boundary_eq
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.cycle_eq
#check @FilteredComplex.Cohomology.Convergence.IsWeakAlong.of_equalities
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
