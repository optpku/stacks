module

public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 12.24.10 (1) [012V]: for an associated spectral sequence, equality of the eventual
and intrinsic boundary and cycle representatives gives weak convergence.  The formal statement
does not reverse this implication from an arbitrary isomorphism of quotient objects. -/
@[stacks 012V]
#check FilteredComplex.Cohomology.Representative.IsWeak.convergence

/- Lemma 12.24.10 (2) [012V]: the representative weak-convergence and filtration criteria give
abutment. -/
@[stacks 012V]
#check FilteredComplex.Cohomology.Representative.IsWeak.abuts

/- The intrinsic separatedness/exhaustiveness formulation is available independently of a
chosen associated spectral sequence. -/
#check FilteredComplex.Cohomology.Representative.IsSeparatedExhaustive.iff_filtration
