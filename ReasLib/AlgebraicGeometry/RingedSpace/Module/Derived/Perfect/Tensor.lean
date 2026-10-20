module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor

@[expose] public section

/-!
# Perfect derived tensor products on ringed spaces

The canonical derived tensor product on `D(𝒪_X)` preserves perfect objects.  Its construction and
the instances establishing derivability are owned by the corresponding derived-tensor leaves, so
the public theorem only mentions the mathematical objects involved.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect. -/
@[stacks 09J5]
theorem IsPerfect.tensor {K L : ModuleDerived X}
    [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)]
    (hK : IsPerfect K) (hL : IsPerfect L) :
    IsPerfect (K ⊗ᴸ L) := sorry

/-- The K-flat tensor product of two perfect derived modules on a ringed space is perfect. -/
theorem IsPerfect.kFlatTensor
    [KFlat.HomotopyTensorDescends X]
    [KFlat.TensorDescends X]
    [KFlat.IsLocalization X]
    {E F : ModuleDerived X}
    (hE : IsPerfect E) (hF : IsPerfect F) :
    IsPerfect (CategoryTheory.MonoidalCategory.tensorObj E F) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
