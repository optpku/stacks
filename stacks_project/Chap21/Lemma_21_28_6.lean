module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.28.6 (0D7V) is a source-facing recall of the restricted derived pullback--pushforward
interface.  The reusable owners are in `RingedSite.Hom.moduleDerivedCohomologyIn`; this chapter
file deliberately introduces no second cohomology-in property, restricted functor, or adjunction
owner.

The canonical root statement is `pullback_isEquivalence`; its landing and restricted-functor
companions remain separately available for proofs that need only one half of the construction.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace RingedSite.Hom.moduleDerivedCohomologyIn

@[stacks 0D7V]
#check @mapsPullbackDerived

@[stacks 0D7V]
#check @pullbackDerived

@[stacks 0D7V]
#check @mapsPushforwardDerived

@[stacks 0D7V]
#check @pushforwardDerived

@[stacks 0D7V]
#check @pullback_isEquivalence

end RingedSite.Hom.moduleDerivedCohomologyIn

end
