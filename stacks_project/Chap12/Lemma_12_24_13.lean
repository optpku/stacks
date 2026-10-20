module

public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 12.24.13 hypotheses [0BK5]: stage cohomology eventually vanishes above and stabilizes
below. -/
#check FilteredComplex.StageCohomology.eventuallyVanishesAbove
#check FilteredComplex.StageCohomology.eventuallyStabilizesBelow

/- Standard acyclicity and quasi-isomorphism formulations imply the stagewise criteria. -/
#check FilteredComplex.StageCohomology.eventuallyVanishesAbove_of_acyclic
#check FilteredComplex.StageCohomology.eventuallyStabilizesBelow_of_quasiIso

/- Lemma 12.24.13 (1) [0BK5]: every associated spectral sequence is bounded. -/
@[stacks 0BK5]
#check FilteredComplex.StageCohomology.associated_isBounded

/- Lemma 12.24.13 (2) [0BK5]: every induced cohomology filtration is finite. -/
@[stacks 0BK5]
#check FilteredComplex.StageCohomology.Cohomology.isFinite

/- Lemma 12.24.13 (3) [0BK5]: every associated spectral sequence converges to cohomology. -/
@[stacks 0BK5]
#check FilteredComplex.StageCohomology.associated_converges
