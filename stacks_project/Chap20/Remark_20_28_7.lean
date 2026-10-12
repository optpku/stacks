/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import StacksCheckRecall

@[expose] public section

/- [stacks 0B68] Remark 20.28.7: the relative cup product for derived module pushforward is the
tensorator of its canonical lax monoidal structure. -/

namespace RingedSite.Hom.modulePushforwardDerived

#check @laxMonoidal
@[stacks 0B68] #check @cupProduct
#check @map_cupProduct_comp_counit

end RingedSite.Hom.modulePushforwardDerived

#check @AlgebraicGeometry.RingedSpace.opensRingedSiteHom
