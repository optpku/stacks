module

import StacksCheckRecall
public import Mathlib.RingTheory.Binomial
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import stacks_project.Chap42.«42_39_1_1»
public import stacks_project.Chap42.Lemma_42_46_10_Rank
public import stacks_project.Chap42.Remark_42_46_8

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry

open RingedSpace
open ModuleDerived

namespace RingedSpace
namespace ModuleDerived
namespace IsPerfect

/-- Tensoring a perfect derived module by an invertible module concentrated in degree zero
preserves perfectness. -/
theorem tensorInvertible {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    {E : ModuleDerived X.toRingedSpace}
    (hPerfect : ModuleDerived.IsPerfect E)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    ModuleDerived.IsPerfect
      (E ⊗ᴸ (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj L) := sorry

end IsPerfect
end ModuleDerived
end RingedSpace

namespace ChernClass
namespace Derived

namespace IsDefined

/-- Tensoring by an invertible module concentrated in degree zero preserves the definedness
of derived Chern classes. -/
theorem tensorInvertible {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    {E : ModuleDerived X.toRingedSpace} (hDefined : IsDefined E)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    IsDefined
      (E ⊗ᴸ (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj L) := sorry

end IsDefined

/-- Lemma 42.46.10: If the perfect derived module `E` has constant virtual rank `r`, then
tensoring by an invertible module `L` changes its `i`-th Chern class by the generalized
binomial formula. -/
@[stacks 0FAF]
theorem totalClass_tensor_invertible
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (classes : ChernClass.Theory δ π)
    (E : ModuleDerived X.toRingedSpace) (L : X.Modules)
    [Scheme.Modules.Invertible L]
    (hPerfect : ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (r : ℤ) (hRank : Scheme.ModuleDerived.IsConstantRank E r) (i : ℕ) :
    ChernClass.homogeneous δ π i
        (totalClass δ π classes
          (E ⊗ᴸ (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj L)
          (hPerfect.tensorInvertible L) (hDefined.tensorInvertible L) i) =
      ∑ j ∈ Finset.range (i + 1),
        (Ring.choose (r - (i : ℤ) + (j : ℤ)) j : ℤ) •
          (ChernClass.homogeneous δ π (i - j)
              (totalClass δ π classes E hPerfect hDefined (i - j)) *
            ChernClass.homogeneous δ π 1 (classes.component L 1) ^ j) := sorry

end Derived
end ChernClass
end AlgebraicGeometry
