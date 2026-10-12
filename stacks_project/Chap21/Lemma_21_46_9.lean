/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.IdealPowerQuotient
import StacksCheckRecall

/-!
# Lemma 21.46.9

The quotient-power sites, their canonical derived pullbacks, and the Tor-amplitude propagation
API are owned by the corresponding ReasLib leaf.
-/

@[expose] public section

/- Lemma 21.46.9 (1) (0942): reduction modulo `I` controls one uniform upper bound after
reduction modulo every positive power of `I`. -/
@[stacks 0942] #check
  @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.pullbackDerived_uniformlyBoundedAbove

#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.pullbackDerived_isLE

/- Lemma 21.46.9 (2) (0942): reduction modulo `I` controls the same Tor-amplitude interval
after reduction modulo every positive power of `I`. -/
@[stacks 0942] #check
  @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.pullbackDerived_hasTorAmplitudeIn

#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.ringedSite
#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.projectionHom
#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.pullbackDerived

end
