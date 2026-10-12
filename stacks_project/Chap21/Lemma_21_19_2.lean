/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Canonical
import StacksCheckRecall

@[expose] public section

/- Lemma 21.19.2 (0D6E): iterated derived module pushforward is canonically isomorphic to
derived pushforward along the composite morphism of ringed sites. -/
@[stacks 0D6E]
#check @RingedSite.Hom.modulePushforwardDerived.compIso

#check @RingedSite.Hom.modulePushforwardDerived.compComparison
#check @RingedSite.Hom.modulePushforwardDerived.compIso_hom_counit
