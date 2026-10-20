module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.33.2

Associativity of the relative derived cup product is exactly the associativity law of the
canonical lax monoidal derived pushforward.
-/

/- Lemma 21.33.2 (0FPL): the relative derived cup product is associative. -/
@[stacks 0FPL]
#check @RingedSite.Hom.modulePushforwardDerived.cupProduct_assoc

#check @RingedSite.Hom.modulePushforwardDerived.cupProduct
