/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Colimit
import StacksCheckRecall

@[expose] public section

/-!
# Exact-colimit support for Lemma 21.17.10

The former chapter-local construction of degree short complexes duplicated the generic
homological-complex colimit API.  This file is retained as a compatibility import surface only.
-/

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.17.10 (077J): exact colimits commute with homology, and the comparison on each
colimit leg is the canonical homology map. -/
@[stacks 077J "exact-colimit homology comparison"]
#check @HomologicalComplex.homologyColimitIso

#check @HomologicalComplex.homologyColimitIso_hom_ι
#check @HomologicalComplex.homologyColimitIso_inv_homologyMap_ι

/- The generic quasi-isomorphism criterion used for the colimit map in Lemma 21.17.10. -/
#check @HomologicalComplex.quasiIso_colimitDesc_of_mapCocone_isColimit

/- Exact colimits of any diagram shape preserve homology. -/
#check @HomologicalComplex.homologyFunctor_preservesColimitsOfShape_of_exact

end
