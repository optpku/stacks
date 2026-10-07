module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.Supported
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.2 (0AEF): derived direct image from a closed subset identifies its derived module
category with the full subcategory of ambient derived modules whose cohomology is supported on the
closed subset.  This full subcategory is coreflective, with coreflector `i_* ∘ R𝓗_Z`. -/

#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SupportedDerived
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.SupportedOn.inclusion
#check @SheafOfModules.ClosedSubset.Derived.Pushforward.mem_essImage_iff_supported
#check @SheafOfModules.ClosedSubset.Derived.Pushforward.obj_supported
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward.toSupported
#check @SheafOfModules.ClosedSubset.Derived.Pushforward.toSupportedCompιIso
#check @SheafOfModules.ClosedSubset.Derived.Pushforward.toSupported_isEquivalence
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SupportedDerived.coreflector
@[stacks 0AEF]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SupportedDerived.adjunction
#check @SheafOfModules.ClosedSubset.SupportedDerived.inclusionCoreflective
