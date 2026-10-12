/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Pushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 21.21.2 (0FN5): for the cartesian square of localization morphisms induced by
`X' ⟶ X` over `Y' ⟶ Y`, restriction of `Rj_{X/Y,*}` to `Y'` is naturally isomorphic to first
restricting to `X'` and then applying `Rj_{X'/Y',*}`.  The reusable owner states this for an
arbitrary ringed-site morphism followed by localization. -/
@[stacks 0FN5]
#check @RingedSite.Hom.LocalizedPushforward.iso

#check @RingedSite.Hom.LocalizedPushforward.appIso
