module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedCohomology
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.25.6 (0D6W).  The source's Situation `21.25.5` hypothesis is represented by the
explicit `RingedSite.Hom.BoundedCohomologyBasis f A` owner.  It is part of the public statement,
because it records the target-site covers and the vanishing after pullback; it is not replaced by
the weaker site-only basis from Lemma 21.25.4.
-/

open CategoryTheory

@[stacks 0D6W]
#check @RingedSite.Hom.modulePushforwardDerived.homologyMap_isIso_of_pullbackBasis

#check @RingedSite.Hom.modulePushforwardDerived.lowerStageMap
#check @RingedSite.Hom.BoundedCohomologyBasis
#check @RingedSite.Hom.PullbackBasis
#check @CategoryTheory.Functor.hasCohomologicalDimensionLEOn_iff

end
