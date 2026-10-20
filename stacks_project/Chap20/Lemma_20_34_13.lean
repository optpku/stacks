module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections.BaseChange
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.13 (0G79): the canonical pullback map on derived global sections with support is
obtained by transporting ambient derived pullback across the closed-subset base-change mate and
the supported-to-ambient comparison. It commutes with forgetting support, both in the derived
category and after applying degree-`n` homology.

The concrete map, its ambient-model specification, and the two commutative squares are owned by
`AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange`. -/

@[stacks 0G79]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.map
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.app
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.map_comp_targetComparison
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.app_comp_targetComparison
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.map_comp_forget
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.forgetCommSq
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.cohomologyApp
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange.cohomologyCommSq
