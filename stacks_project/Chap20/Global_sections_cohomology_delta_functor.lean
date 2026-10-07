module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Delta
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- This source item is a canonical recall: the reusable declarations live in
`Module.Derived.GlobalSections.Delta`.  The checks below preserve the source tags without adding
chapter-owned aliases. -/

@[stacks 0150]
#check @Module.Derived.GlobalSections.Delta.single

@[stacks 0151]
#check @Module.Derived.GlobalSections.Delta.derived

@[stacks 05SR]
#check @Module.Derived.GlobalSections.Delta.hneg

@[stacks 05SR]
#check @Module.Derived.GlobalSections.Delta.cohomology

@[stacks 0EHA]
#check @Module.Derived.GlobalSections.Delta.degree_obj_eq_moduleCohomologyAtOpen

@[stacks 0EHA]
#check @Module.Derived.GlobalSections.Delta.map_smul

end AlgebraicGeometry.RingedSpace
