module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.10

Flatness makes module pullback exact, so its right adjoint preserves K-injective complexes.
-/

/- Lemma 21.20.10 (093Y): direct image along a flat morphism of ringed sites preserves
K-injective cochain complexes. -/
@[stacks 093Y]
#check @RingedSite.Hom.modulePushforwardComplex.isKInjective

#check @RingedSite.Hom.IsFlat.exactPullback
#check @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint
