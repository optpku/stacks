module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Comparison
public import ReasLib.Topology.Category.LCCat.Covering
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.31.9 (0EZI) is the concrete `LC_qc`/`LC_Zar` comparison package.  The reusable
coefficient object is the essential image of the canonical abelian inverse image on the Zariski
slice; arbitrary topology or site-functor parameters would lose the source hypotheses.  The
canonical data and the closure facts are owned by `LCCat.SmallToSlice` and `LCCat`; this chapter
file is deliberately recall-only.
-/

open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open TopologicalSpace

/- Lemma 21.31.9 (1): the proper morphism property has pullbacks. -/
@[stacks 0EZI "(1)"]
#check @LCCat.proper_hasPullbacks

/- Lemma 21.31.9 (2): proper morphisms are stable under base change. -/
@[stacks 0EZI "(2)"]
#check @LCCat.proper_isStableUnderBaseChange

/- The source coefficient family `A'_X = essImage (π_X⁻¹)` is a canonical object property. -/
@[stacks 0EZI "essential-image coefficient family"]
#check @LCCat.SmallToSlice.essImageAb

/- The weak-Serre clause is stated on the canonical localized Zariski abelian category. -/
@[stacks 0EZI "weak Serre coefficient family"]
#check @LCCat.SmallToSlice.essImageAb_isWeakSerre

/- Lemma 21.31.9 (3): inverse image along a morphism preserves the essential image. -/
@[stacks 0EZI "(3)"]
#check @LCCat.SmallToSlice.essImageAb_inverseImage_mem

/- Lemma 21.31.9 (4): essential-image coefficients satisfy the qc sheaf condition. -/
@[stacks 0EZI "(4)"]
#check @LCCat.SmallToSlice.essImageAb_isSheafQc

/- The objectwise cohomology comparison used by the source-facing cohomology clause. -/
@[stacks 0EZI "cohomology comparison"]
#check @LCCat.SmallToSlice.cohomology_isomorphic

/- Lemma 21.31.9: the five source clauses are packaged by the concrete comparison situation. -/
@[stacks 0EZI]
#check @LCCat.SmallToSlice.comparisonSituation

end
