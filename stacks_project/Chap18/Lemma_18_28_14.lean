module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Criteria
import StacksCheckRecall

/-!
# Lemma 18.28.14

Flat module sheaves are characterized by local factorization of rank-one relations, equivalently
of arbitrary finite matrices.  The reusable leaf exposes the underlying local factorization
predicate and direct `_iff_` lemmas, so downstream users need not unpack `List.TFAE`.
-/

@[expose] public section

open SheafOfModules.RingedSite.FlatCriterion

/- Lemma 18.28.14 (08FC): the three flatness criteria are equivalent. -/
@[stacks 08FC]
#check @isFlat_tfae

/- Fine-grained criteria and their direct bridges. -/
#check @FactorsLocally
#check @SingleRelation
#check @Matrix
#check @isFlat_iff_singleRelation
#check @singleRelation_iff_matrix
#check @isFlat_iff_matrix
