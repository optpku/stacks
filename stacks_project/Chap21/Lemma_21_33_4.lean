/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Monoidal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.33.4

The reusable statement is the monoidal compatibility of the canonical derived-pushforward
composition comparison. Relative cup products are the tensorators of the canonical lax monoidal
derived pushforward functors.
-/

/- Lemma 21.33.4 (0FPN): the relative derived cup product is compatible with composition of
morphisms of ringed topoi. -/
@[stacks 0FPN]
#check @RingedSite.Hom.modulePushforwardDerived.cupProduct_compComparison

#check @RingedSite.Hom.modulePushforwardDerived.cupProduct
#check @RingedSite.Hom.modulePushforwardDerived.compComparison
