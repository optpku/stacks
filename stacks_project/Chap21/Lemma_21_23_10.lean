module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.10

The reusable owner is the uniform negative-basis truncation-comparison criterion in ReasLib.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.10 (0D6P): a uniform negative-degree vanishing bound makes a compatible
lower-truncation comparison an isomorphism. -/
@[stacks 0D6P]
#check @Comparison.isIso_of_uniformNegative

#check @Basis.uniformNegative
#check @Basis.uniformNegative.vanish_sub
#check @Basis.uniformNegative.toEventual
