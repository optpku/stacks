module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.PrincipalAnnihilator.PowerLift

@[expose] public section

/- Lemma 16.7.3 constructs the eighth-power specialization of the reusable
principal-power lift from the source-facing pair of reduction maps. -/
@[stacks 07F0]
#check @AlgHom.Factorisation.Finite.PrincipalPowerLift.nonempty_ofMaps

#check @AlgHom.Factorisation.Through
#check @AlgHom.Factorisation.Through.ofMaps
#check @AlgHom.Factorisation.Finite.PrincipalPowerLift
#check @AlgHom.Factorisation.Finite.PrincipalPowerLift.spec
#check @AlgHom.Factorisation.Finite.PrincipalPowerLift.nonempty_of_principalAnnihilator
#check @Algebra.PrincipalQuotient.mk
#check @Algebra.PrincipalQuotient.map
#check @RingHom.singularIdealIn
#check @Localization.awayMap
#check @Module.IsTorsionStable
