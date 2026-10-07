module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.7.5: modules over `R` are canonically equivalent to quasi-coherent modules on
`Spec R`. -/
@[stacks 01IB] #check tildeEquiv
#check tilde.toTildeΓNatIso
#check Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
