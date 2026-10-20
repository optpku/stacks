module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.4 (0G70): derived global sections with support are canonically identified with
derived sections with support followed by closed-subset direct image and ambient derived global
sections. The comparison, its invertibility, and the compatible forget-support map are owned by
`AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport`. -/

#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.model
@[stacks 0G70]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.comparisonIsIso
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.comparison
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.comparisonIso
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.comparison_fac

#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.ambientComparison
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.ambientComparisonIsIso
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.ambientForget
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.forgetDerived
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.forgetDerived_eq
