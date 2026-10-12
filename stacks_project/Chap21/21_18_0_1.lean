/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Continuous
import StacksCheckRecall

@[expose] public section

/- The site-presented structure map and its module direct/inverse images are canonical ReasLib
owners.  This auxiliary chapter file is only a compatibility recall surface. -/
#check @SheafOfModules.RingedSite.moduleStructureMap
#check @SheafOfModules.RingedSite.modulePushforward
#check @SheafOfModules.RingedSite.modulePullback
#check @SheafOfModules.RingedSite.modulePullback_additive
#check @SheafOfModules.RingedSite.modulePullbackComplex
#check @SheafOfModules.RingedSite.modulePullbackComplex.obj_X

/- Same-site change of structure sheaf is represented by a bundled ringed-site morphism; its
module pullback, adjunction, and extension-of-scalars view are shared ReasLib data. -/
#check @SheafOfModules.RingedSite.sameSiteHom
#check @RingedSite.Hom.modulePullback
#check @RingedSite.Hom.modulePullbackPushforwardAdjunction
#check @RingedSite.Hom.modulePullback_additive
#check @SheafOfModules.RingedSite.extendAlong
#check @SheafOfModules.RingedSite.pullbackExtendIso
