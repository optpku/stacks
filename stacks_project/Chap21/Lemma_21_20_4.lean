module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Pushforward
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.4

The localized derived pushforward comparison is owned by
`RingedSite.Hom.LocalizedPushforward` in `ReasLib`.  This chapter file is a recall surface only:
the underived comparison, its homotopy transport, the two right-derived units, and the functor
and component isomorphisms are all checked directly from that namespace.
-/

/- Lemma 21.20.4 (0D6G): for `f : X ⟶ Y`, `V : Y`, and a derived module `E`, the restriction of
`Rf_* E` to `Y/V` is canonically isomorphic to the direct image along `f.localization V` of the
restriction of `E` to `X/f(V)`. -/
@[stacks 0D6G "underived localization comparison"]
#check @RingedSite.Hom.LocalizedPushforward.underivedIso

@[stacks 0D6G "homotopy localization comparison"]
#check @RingedSite.Hom.LocalizedPushforward.homotopyIso

@[stacks 0D6G "localized source right-derived model"]
#check @RingedSite.Hom.LocalizedPushforward.sourceUnit

@[stacks 0D6G "localized target right-derived model"]
#check @RingedSite.Hom.LocalizedPushforward.targetUnit

@[stacks 0D6G "derived localization comparison"]
#check @RingedSite.Hom.LocalizedPushforward.iso

@[stacks 0D6G "derived localization comparison component"]
#check @RingedSite.Hom.LocalizedPushforward.appIso
