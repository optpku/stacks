module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.ColimitComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

/- Lemma 20.15.0.1 (09UZ): global Cech cohomology is the colimit of the
open-cover refinement diagram.  The reusable owners are in
`TopCat.Sheaf.Cohomology.Cech`; this chapter entry is intentionally a recall
surface and introduces no chapter-local carrier or diagram. -/
@[stacks 09UZ]
#check @TopCat.Sheaf.Cohomology.Cech.refinementDiagram
#check @TopCat.Sheaf.Cohomology.Cech.liftedDiagram
#check @TopCat.Sheaf.Cohomology.Cech.cohomologyFunctor
#check @TopCat.Sheaf.Cohomology.Cech.cohomology
#check @TopCat.Sheaf.Cohomology.Cech.stageFunctor
#check @TopCat.Sheaf.Cohomology.Cech.stageCohomology
#check @TopCat.Sheaf.Cohomology.Cech.stageι
#check @TopCat.Sheaf.Cohomology.Cech.stageMap
#check @TopCat.Sheaf.Cohomology.Cech.cohomologyFunctorIso
#check @TopCat.Sheaf.Cohomology.Cech.liftedTargetCohomology
#check @TopCat.Sheaf.Cohomology.Cech.RefinementComparison
#check @TopCat.Sheaf.Cohomology.Cech.comparison
#check @TopCat.Sheaf.Cohomology.Cech.Comparison
#check @TopCat.Sheaf.Cohomology.Cech.Comparison.isIso_app
#check @TopCat.Sheaf.Cohomology.Cech.Comparison.iso
