/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Tensor
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

/-- Perfect complexes remain perfect under the already specified K-flat tensor.
Locally finite-free representatives tensor to finite-free representatives; this
law concerns the existing tensor object and selects no resolution or object. -/
theorem isPerfect_kFlatTensor {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hF : RingedSpace.ModuleDerived.IsPerfect F) :
    RingedSpace.ModuleDerived.IsPerfect
      (CategoryTheory.MonoidalCategory.tensorObj E F) :=
  RingedSpace.ModuleDerived.IsPerfect.kFlatTensor hE hF


/- Lemma 42.46.11 (1): The first Chern class of a derived tensor product is the virtual-rank-weighted sum
of the first Chern classes of its factors. -/
@[stacks 0FAG] #check (AlgebraicGeometry.ChernClass.Derived.totalClass_tensor_one :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F),
    ChernClass.homogeneous δ π 1
        (totalClass δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) 1) =
      ChernClass.homogeneous δ π 0 (rankClass δ π E hEPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes F hFPerfect hFDefined 1) +
        ChernClass.homogeneous δ π 0 (rankClass δ π F hFPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hEPerfect hEDefined 1))

/- Lemma 42.46.11 (2): The second Chern class of a derived tensor product has the five-term integral
expansion in the Chern classes and generalized binomial virtual-rank classes of its factors. -/
@[stacks 0FAG] #check (AlgebraicGeometry.ChernClass.Derived.totalClass_tensor_two :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F),
    ChernClass.homogeneous δ π 2
        (totalClass δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) 2) =
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
            (totalClass δ π classes E hEPerfect hEDefined 1) ^ 2)

/- Lemma 42.46.11 (3): The degree components of the Chern character of a derived tensor product are
the convolution of the components of the Chern characters of its factors. -/
@[stacks 0FAG] #check (AlgebraicGeometry.ChernClass.Derived.character_tensor :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ),
    ChowCohomology.Nonnegative.rationalHomogeneous δ π p
        (character δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        ChowCohomology.Nonnegative.rationalHomogeneous δ π j
            (character δ π classes E hEPerfect hEDefined j) *
          ChowCohomology.Nonnegative.rationalHomogeneous δ π (p - j)
            (character δ π classes F hFPerfect hFDefined (p - j)))

/- Lemma 42.46.11 (4): The Newton classes of a derived tensor product are the binomial convolution
of the Newton classes of its factors. -/
@[stacks 0FAG] #check (AlgebraicGeometry.ChernClass.Derived.newtonClass_tensor :
    ∀
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ),
    ChernClass.homogeneous δ π p
        (newtonClass δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        p.choose j •
          (ChernClass.homogeneous δ π j
              (newtonClass δ π classes E hEPerfect hEDefined j) *
            ChernClass.homogeneous δ π (p - j)
              (newtonClass δ π classes F hFPerfect hFDefined (p - j))))

end AlgebraicGeometry.ChernClass.Derived
