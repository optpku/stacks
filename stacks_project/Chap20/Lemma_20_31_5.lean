module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- [stacks 0FP4] Lemma 20.31.5: the relative cup product is associative because it is the
tensorator of the canonical lax monoidal structure on derived pushforward. -/

namespace RingedSite.Hom.modulePushforwardDerived

#check @cupProduct
#check @laxMonoidal
@[stacks 0FP4] #check @Functor.LaxMonoidal.associativity

end RingedSite.Hom.modulePushforwardDerived
