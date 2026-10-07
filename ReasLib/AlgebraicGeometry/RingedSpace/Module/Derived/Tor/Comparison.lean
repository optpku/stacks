module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor.Right
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tor.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Comparison of ringed-space Tor models

This leaf identifies the fixed-right Tor presentation used by `- ⊗ᴸ L` with the source-facing
two-variable Tor object.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [Tensor.Has X]

/-- The fixed-right Tor functor agrees naturally with the fixed-right view of bifunctorial Tor. -/
@[stacks 08BP "ringed-space fixed-right Tor functor comparison"]
noncomputable abbrev torRightFunctorIsoTor (p : ℕ) (L : ModuleDerived X) :
    torRightFunctor p L ≅
      DerivedCategory.DerivedTensor.Bifunctor.torRightFunctor p L :=
  DerivedCategory.DerivedTensor.torRightFunctorIsoTor p L

/-- The fixed-right and bifunctorial Tor objects agree on arbitrary derived modules. -/
@[stacks 08BP "ringed-space fixed-right Tor comparison"]
noncomputable abbrev torRightObjIsoTor (p : ℕ) (K L : ModuleDerived X) :
    torRightObj p K L ≅ torObj p K L :=
  (torRightFunctorIsoTor p L).app K

/-- The fixed-right and bifunctorial Tor objects agree on ordinary module sheaves. -/
@[stacks 08BP "ringed-space degree-zero fixed-right Tor comparison"]
noncomputable abbrev torRightIsoTor (p : ℕ) (F G : Modules X) :
    torRight p F G ≅ tor p F G :=
  DerivedCategory.DerivedTensor.torRightIsoTor p F G

end AlgebraicGeometry.RingedSpace.ModuleDerived

end
