module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible
import StacksCheckRecall

@[expose] public section

/- The source-facing local shifted-invertible owner and Lemma 21.49.2 (3) now live in ReasLib.
This historical path retains a discoverable recall instead of an empty aggregation module. -/
@[stacks 0FPY "local shifted-invertibility predicate"]
#check @RingedSite.Hom.ModuleDerived.IsLocallyShiftedInvertible

@[stacks 0FPY "local shifted-invertibility criterion"]
#check @SheafOfModules.RingedSite.isInvertible_iff_isLocallyShiftedInvertible
