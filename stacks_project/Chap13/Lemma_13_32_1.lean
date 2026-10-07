module

import ReasLib.Algebra.Homology.CochainComplex.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.32.1

The categorical dimension axioms and the complex-level replacement theorem
are owned by separate ReasLib modules.  This chapter file records the
source-facing entry points without retaining a private truncation-and-splicing
implementation.
-/

/- The categorical hypotheses of Lemma 13.32.1 are packaged by a cohomological-dimension
function and exposed in source form by this characterization. -/
#check @CategoryTheory.CohomologicalDimension.IsFunction.axioms_iff

/- The shifted-dimension convergence condition records both eventual finiteness and convergence
of `n + d (K.X n)` toward `-∞`. -/
#check @CochainComplex.ShiftedDimension.TendstoNegInf

/- The canonical object-property form of the replacement theorem places every term in the zero
locus of `d`. -/
#check @CochainComplex.ShiftedDimension.TendstoNegInf.existsQuasiIso

/- Lemma 13.32.1 (Stacks 07K6): under the three cohomological-dimension axioms and the
shifted-dimension convergence hypothesis, there is a quasi-isomorphic complex whose terms all
have dimension zero. -/
@[stacks 07K6]
#check @CochainComplex.ShiftedDimension.TendstoNegInf.existsQuasiIso_zero
