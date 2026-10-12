/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.4: pullback along a morphism of ringed spaces preserves flat module sheaves. This is
the specialization of the canonical ringed-site instance to `RingedSpace.opensRingedSiteHom`. -/
@[stacks 0H97]
#check @SheafOfModules.RingedSite.IsFlat.modulePullback

/- Companion recall: a morphism of ringed spaces induces the corresponding morphism of its opens
ringed sites. -/
#check @AlgebraicGeometry.RingedSpace.opensRingedSiteHom

/- Companion recall: the ringed-space pullback is the module pullback attached to its
structure-sheaf morphism. -/
#check @AlgebraicGeometry.RingedSpace.Hom.pullback
