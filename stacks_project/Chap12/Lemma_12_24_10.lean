module

public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 12.24.10 (1) [012V]: an associated spectral sequence weakly converges if and only if
the eventual and intrinsic boundary and cycle representatives agree. -/
@[stacks 012V]
#check FilteredComplex.Cohomology.Representative.IsWeak.convergence_iff
#check FilteredComplex.Cohomology.Representative.IsWeak.convergence

/- Lemma 12.24.10 (2) [012V]: an associated spectral sequence abuts if and only if the
representative weak-convergence and filtration criteria hold. -/
@[stacks 012V]
#check FilteredComplex.Cohomology.Representative.IsWeak.abuts_iff
#check FilteredComplex.Cohomology.Representative.IsWeak.abuts

/- The intrinsic separatedness/exhaustiveness formulation is available independently of a
chosen associated spectral sequence. -/
#check FilteredComplex.Cohomology.Representative.IsSeparatedExhaustive.iff_filtration
