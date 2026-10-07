module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.ComplexTower
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- The chapter-level names are now recalls of the reusable ReasLib tower owner. -/
@[stacks 08CT]
#check @RingedSite.Hom.ModuleSections.Underlying.complexDegree
#check @RingedSite.Hom.ModuleSections.Underlying.complexDegreeTower
#check @RingedSite.Hom.ModuleSections.Underlying.complexCohomology
#check @RingedSite.Hom.ModuleSections.Underlying.complexCohomologyTower
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologySheaf
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologySheafTower
#check @RingedSite.Hom.complexSectionDegreeFunctor
#check @RingedSite.Hom.complexSectionDegreeInverseSystem
#check @RingedSite.Hom.complexSectionCohomologyFunctor
#check @RingedSite.Hom.complexSectionCohomologyInverseSystem
#check @RingedSite.Hom.underlyingAbelianCohomologySheafFunctor
#check @RingedSite.Hom.underlyingAbelianCohomologySheafInverseSystem
