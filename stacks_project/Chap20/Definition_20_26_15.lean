/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor
import StacksCheckRecall

@[expose] public section

/- Definition 20.26.15: for a ringed space, `Tor[p](ℱ, 𝒢)` is the degree-`-p` homology of the
derived tensor of the two degree-zero module objects.  The reusable owner is
`RingedSpace.ModuleDerived.tor`; its generic source is `DerivedTensor.Bifunctor.tor`. -/

open AlgebraicGeometry CategoryTheory
open scoped DerivedTor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [ModuleDerived.Tensor.Has X]
variable (p : ℕ) (ℱ 𝒢 : Modules X)

@[stacks 08BP "Tor of ringed-space modules via derived tensor"]
#check @ModuleDerived.tor

#check (ModuleDerived.tor p ℱ 𝒢 : Modules X)
#check (Tor[p](ℱ, 𝒢) : Modules X)
#check @ModuleDerived.torObj
#check @ModuleDerived.torFunctor
#check @ModuleDerived.torRightFunctor
#check @ModuleDerived.torRightObj
#check @ModuleDerived.torRight
#check @ModuleDerived.torLeftFunctor
#check @ModuleDerived.torLeftObj
#check @ModuleDerived.torLeft
#check @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.torObj
#check @CategoryTheory.DerivedCategory.DerivedTensor.torRightObj

end AlgebraicGeometry.RingedSpace

end
