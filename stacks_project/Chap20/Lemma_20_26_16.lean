module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 20.26.16: an `𝒪_X`-module is flat exactly when its first Tor with every
`𝒪_X`-module vanishes.  Tor is the source-facing two-variable derived-tensor owner. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedTor

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [ModuleDerived.Tensor.Has X]
variable (F : Modules X)

@[stacks 08BQ "flatness detected by first Tor"]
#check @ModuleDerived.Tor.isFlat_iff_isZero_tor_one

#check
  (ModuleDerived.Tor.isFlat_iff_isZero_tor_one F :
    F.IsFlat ↔ ∀ G : Modules X, IsZero (Tor[1](F, G)))

#check @ModuleDerived.Tor.isZero_tor_one_of_isFlat
#check @ModuleDerived.Tor.isFlat_of_isZero_tor_one

end AlgebraicGeometry.RingedSpace

end
