module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import stacks_project.Chap42.Lemma_42_43_4
public import stacks_project.Chap42.Lemma_42_45_3
public import stacks_project.Chap42.Lemma_42_46_11_VirtualRank
public import stacks_project.Chap42.Remark_42_46_8

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived

namespace IsDefined

/-- Definedness of derived Chern classes is preserved by derived tensor products. -/
theorem tensor {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    IsDefined (E ⊗ᴸ F) := sorry

end IsDefined

/-- Lemma 42.46.11 (1): the first Chern class of a derived tensor product is
`rankClass(E) * c₁(F) + rankClass(F) * c₁(E)`. -/
@[stacks 0FAG]
theorem totalClass_tensor_one
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    ChernClass.homogeneous δ π 1
        (totalClass δ π classes (E ⊗ᴸ F) (hEPerfect.tensor hFPerfect)
          (hEDefined.tensor hFDefined) 1) =
      ChernClass.homogeneous δ π 0 (rankClass δ π E hEPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes F hFPerfect hFDefined 1) +
        ChernClass.homogeneous δ π 0 (rankClass δ π F hFPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hEPerfect hEDefined 1) := sorry

/-- Lemma 42.46.11 (2): the second Chern class of a derived tensor product has the
five-term virtual-rank expansion. -/
@[stacks 0FAG]
theorem totalClass_tensor_two
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    ChernClass.homogeneous δ π 2
        (totalClass δ π classes (E ⊗ᴸ F) (hEPerfect.tensor hFPerfect)
          (hEDefined.tensor hFDefined) 2) =
      ChernClass.homogeneous δ π 0 (rankClass δ π E hEPerfect) *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes F hFPerfect hFDefined 2) +
        ChernClass.homogeneous δ π 0 (rankClass δ π F hFPerfect) *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hEPerfect hEDefined 2) +
        ChernClass.homogeneous δ π 0 (rankChoose δ π E hEPerfect 2) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes F hFPerfect hFDefined 1) ^ 2 +
        (ChernClass.homogeneous δ π 0 (rankClass δ π E hEPerfect) *
              ChernClass.homogeneous δ π 0 (rankClass δ π F hFPerfect) - 1) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes F hFPerfect hFDefined 1) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hEPerfect hEDefined 1) +
        ChernClass.homogeneous δ π 0 (rankChoose δ π F hFPerfect 2) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hEPerfect hEDefined 1) ^ 2 := sorry

/-- Lemma 42.46.11 (3): the Chern character of a derived tensor product is the
coefficientwise product of the two Chern characters. -/
@[stacks 0FAG]
theorem character_tensor
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ) :
    ChowCohomology.Nonnegative.rationalHomogeneous δ π p
        (character δ π classes (E ⊗ᴸ F) (hEPerfect.tensor hFPerfect)
          (hEDefined.tensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        ChowCohomology.Nonnegative.rationalHomogeneous δ π j
            (character δ π classes E hEPerfect hEDefined j) *
          ChowCohomology.Nonnegative.rationalHomogeneous δ π (p - j)
            (character δ π classes F hFPerfect hFDefined (p - j)) := sorry

/-- Lemma 42.46.11 (4): the degree-`p` Newton class of a derived tensor product is
the binomial convolution of the Newton classes of its factors. -/
@[stacks 0FAG]
theorem newtonClass_tensor
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ) :
    ChernClass.homogeneous δ π p
        (newtonClass δ π classes (E ⊗ᴸ F) (hEPerfect.tensor hFPerfect)
          (hEDefined.tensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        p.choose j •
          (ChernClass.homogeneous δ π j
              (newtonClass δ π classes E hEPerfect hEDefined j) *
            ChernClass.homogeneous δ π (p - j)
              (newtonClass δ π classes F hFPerfect hFDefined (p - j))) := sorry

end AlgebraicGeometry.ChernClass.Derived
