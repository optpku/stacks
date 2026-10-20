module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.7.3: along an affine spectrum map, geometric pullback and pushforward correspond to
extension and restriction of scalars. -/
@[stacks 01I9] #check tilde.ChangeOfRings.Pullback.iso
@[stacks 01I9] #check tilde.ChangeOfRings.Pushforward.iso
#check ModuleSpecΓ.pushforwardIso
#check tilde.ChangeOfRings.GlobalSections.pushforwardIso
#check tilde.ChangeOfRings.Pullback.hom_app_homEquiv
#check tilde.ChangeOfRings.Pullback.inv_app_homEquiv
#check tilde.ChangeOfRings.Pushforward.fromTildeΓ_hom_app
#check tilde.ChangeOfRings.Pushforward.inv_app_fromTildeΓ
#check Scheme.Modules.pullbackPushforwardAdjunction
#check ModuleCat.extendRestrictScalarsAdj
