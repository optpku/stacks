/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.IdealPowerTorsion

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

#check stalkSystem
#check stalkSystem_def
#check stalkLimit
#check stalkLimit_def
#check localRingMap
#check localRingMap_def
#check stalkIdeal
#check stalkIdeal_def
#check openStalkRingEquiv
#check ambientLocalRingMap
#check openStalkRingEquiv_map_stalkIdeal
#check completedLocalRing
#check completedLocalRing_def
#check stalkLimit_isAdicComplete
#check completedStalk
#check completedStalk_def
#check completedIdeal
#check completedIdeal_def
#check completedMaximalIdeal
#check completedMaximalIdeal_def
#check enatToEInt
#check enatToEInt_apply
#check closedFiberOpenPoint
#check closedFiberOpenPoint_image
#check algebraizationClosedSubset
#check algebraizationClosedSubset_def
#check algebraizationDistance
#check algebraizationDistance_apply

end AlgebraicGeometry.Scheme.CoherentFormalModules
