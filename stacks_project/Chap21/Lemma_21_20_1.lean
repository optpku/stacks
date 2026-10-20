module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.1

Localized restriction preserves K-injective complexes because it is right adjoint to exact
extension by zero.
-/

/- Lemma 21.20.1 (08FI): restriction to the localization of a ringed site sends K-injective
cochain complexes to K-injective cochain complexes. -/
@[stacks 08FI]
#check @RingedSite.Hom.localizedRestrictionComplex_isKInjective

#check @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint
#check @SheafOfModules.Localization.lowerShriek.exactOfIsRightAdjoint
