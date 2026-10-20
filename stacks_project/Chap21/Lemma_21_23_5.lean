module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.BasisComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.5

The reusable owner is `RingedSite.Hom.ModuleDerived.Limit.Single`; this file preserves the two
source clauses as tagged recall checks.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.5 (0BKY) (1): a basiswise-acyclic tower has derived limit equal to its ordinary
inverse limit in degree zero. -/
@[stacks 0BKY]
#check @Single.iso_limit_of_basiswise

/- Lemma 21.23.5 (0BKY) (2): the ordinary inverse limit has no positive cohomology on the basis. -/
@[stacks 0BKY]
#check @Single.limit_cohomology_isZero_of_basiswise

#check @basiswiseAcyclic
#check @basiswiseR1Vanishing
