module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Spec

variable {R : CommRingCat.{u}} (I : Ideal R)

/- Example 26.8.1: the spectrum of a quotient is the closed subspace associated to the
quasi-coherent ideal sheaf `Ĩ`. -/
@[stacks 01IG] #check quotientMap_isAssociated I
#check (inferInstance : IsClosedImmersion (quotientMap I))
#check quotientMap.stalkArrowIso I
#check tildeIdeal.ι I
#synth (tilde (ModuleCat.of R I)).IsQuasicoherent
#check tildeIdeal.moduleIso I
#check tildeIdeal.moduleIso_hom_arrow I
#check quotientOverIso I

/- The underlying closed-immersion fact is Mathlib's canonical quotient-spectrum instance. -/
#check IsClosedImmersion.spec_of_quotient_mk

end AlgebraicGeometry.Spec
