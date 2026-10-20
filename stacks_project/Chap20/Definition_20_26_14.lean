module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
import StacksCheckRecall

@[expose] public section

/- Definition 20.26.14: for `L : D(𝒪_X)`, the functor `- ⊗ᴸ L` is the canonical fixed-right
derived tensor functor.  Its comparison with the source-facing two-variable tensor is owned in
ReasLib, so the numbered chapter introduces no second derived-functor construction. -/

open AlgebraicGeometry CategoryTheory
open scoped RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (L : ModuleDerived X)

@[stacks 06YH "fixed-right derived tensor functor"]
#check (derivedTensorProduct L : ModuleDerived X ⥤ ModuleDerived X)

#check @derivedTensorSourceFunctor
#check @derivedTensorProductCounit
#check @derivedTensorProduct_commShift
#check @derivedTensorProduct_isLeftDerivedFunctor
#check @derivedTensorProduct_isTriangulated

#synth (derivedTensorProduct L).CommShift ℤ
#synth (derivedTensorProduct L).IsTriangulated

variable (K : ModuleDerived X) (p : ℕ)

#check K ⊗^L L

end AlgebraicGeometry.RingedSpace

end
