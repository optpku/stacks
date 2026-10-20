module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes and dualizability

For the canonical derived tensor product on `D(𝒪_X)`, perfectness is exactly right
dualizability.  The characterization is independent of a chosen internal-Hom structure; a
right internal Hom is needed only for its derived comparison maps.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]

/-- A perfect derived `𝒪_X`-module is right-dualizable for the canonical derived tensor
product. -/
@[stacks 0FPC "perfect implies right-dualizable"]
theorem IsPerfect.isRightDualizable
    {K : ModuleDerived X} (hK : IsPerfect K) :
    IsRightDualizable K := sorry

/-- A right-dualizable derived `𝒪_X`-module is perfect. -/
@[stacks 0FPD "right-dualizable implies perfect"]
theorem isPerfect_of_isRightDualizable
    {K : ModuleDerived X} (hK : IsRightDualizable K) :
    IsPerfect K := sorry

/-- Perfect derived `𝒪_X`-modules are exactly the right-dualizable objects of `D(𝒪_X)`. -/
@[stacks 0FPC "forward implication", stacks 0FPD "reverse implication"]
theorem isPerfect_iff_isRightDualizable (K : ModuleDerived X) :
    IsPerfect K ↔ IsRightDualizable K := sorry

/-- Lemma 20.50.4 in reusable form: the composition transpose for any chosen right internal Hom
is invertible when its first argument is perfect. -/
@[stacks 0G40 "right-internal-Hom symmetric form"]
theorem IsPerfect.isIso_compTranspose
    {K : ModuleDerived X} (hK : IsPerfect K)
    (H : RightInternalHom (ModuleDerived X)) (L M : ModuleDerived X) :
    IsIso (H.compTranspose K L M) :=
  hK.isRightDualizable.isIso_compTranspose H L M

end AlgebraicGeometry.RingedSpace.ModuleDerived
