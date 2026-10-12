/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.14.1

The reusable owner is the canonical `IsTotallyAcyclic` instance for the
underlying abelian sheaf of the pushforward of an injective module sheaf.
-/

/- Lemma 21.14.1 (072Z): the pushforward of an injective module sheaf along a morphism of
ringed sites has totally acyclic underlying abelian sheaf. -/
@[stacks 072Z]
#check @RingedSite.Hom.modulePushforward.isTotallyAcyclic_of_injective

end
