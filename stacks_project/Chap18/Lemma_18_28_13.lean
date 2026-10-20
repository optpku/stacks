module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings.Flat
import StacksCheckRecall

/-!
# Lemma 18.28.13

Changing scalars along a morphism of commutative ring sheaves preserves flat module sheaves.
The reusable API uses same-site extension of scalars as its owner and supplies the older
ringed-site pullback presentation as a compatibility view.
-/

@[expose] public section

/- Lemma 18.28.13 (05V4): same-site extension of scalars preserves flatness. -/
@[stacks 05V4]
#check @SheafOfModules.RingedSite.IsFlat.extendAlong

/- Compatibility with the same-site pullback presentation. -/
#check @SheafOfModules.RingedSite.IsFlat.pullbackSameSite
