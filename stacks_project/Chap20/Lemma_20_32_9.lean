module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.KInjective

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.KInjective

/-
Lemma 20.32.9 (0D5Z): for a flat morphism `f : X ⟶ Y`, the direct image of a K-injective
cochain complex of `𝒪_X`-modules is K-injective.  The reusable owner factors this through the
generic exact-adjunction transport theorem and registers the result as an instance.
-/

@[stacks 0D5Z "Lemma 20.32.9: flat direct image preserves K-injective complexes"]
#check @isKInjective

@[stacks 0D5Z "flat pushforward homological-complex map"]
#check @complex

end
