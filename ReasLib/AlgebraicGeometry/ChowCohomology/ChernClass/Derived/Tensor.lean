module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.VirtualRank
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Newton
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived

namespace IsDefined

/-- Definedness of derived Chern classes is preserved by K-flat tensor products. -/
theorem tensor {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    IsDefined (CategoryTheory.MonoidalCategory.tensorObj E F) := sorry

end IsDefined

namespace IsDefined

/-- Definedness of derived Chern classes is preserved by the canonical derived tensor product. -/
theorem derivedTensor {X : Scheme.{u}}
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    IsDefined (E ⊗ᴸ F) := sorry

end IsDefined

/-- The first Chern class of a derived tensor product is the virtual-rank-weighted sum
of the first Chern classes of its factors. -/
theorem totalClass_tensor_one
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
    ChernClass.homogeneous δ π 1
        (totalClass δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) 1) =
      ChernClass.homogeneous δ π 0 (rankClass δ π E hEPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes F hFPerfect hFDefined 1) +
        ChernClass.homogeneous δ π 0 (rankClass δ π F hFPerfect) *
          ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hEPerfect hEDefined 1) := sorry

/-- The second Chern class of a derived tensor product has the five-term integral
expansion in the Chern classes and generalized binomial virtual-rank classes of its factors. -/
theorem totalClass_tensor_two
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) :
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
            (totalClass δ π classes E hEPerfect hEDefined 1) ^ 2 := sorry

/-- The degree components of the Chern character of a derived tensor product are
the convolution of the components of the Chern characters of its factors. -/
theorem character_tensor
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ) :
    ChowCohomology.Nonnegative.rationalHomogeneous δ π p
        (character δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        ChowCohomology.Nonnegative.rationalHomogeneous δ π j
            (character δ π classes E hEPerfect hEDefined j) *
          ChowCohomology.Nonnegative.rationalHomogeneous δ π (p - j)
            (character δ π classes F hFPerfect hFDefined (p - j)) := sorry

/-- The Newton classes of a derived tensor product are the binomial convolution
of the Newton classes of its factors. -/
theorem newtonClass_tensor
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E F : RingedSpace.ModuleDerived X.toRingedSpace)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F)
    (hEDefined : IsDefined E) (hFDefined : IsDefined F) (p : ℕ) :
    ChernClass.homogeneous δ π p
        (newtonClass δ π classes (E ⊗ᴸ F) (RingedSpace.ModuleDerived.IsPerfect.tensor hEPerfect hFPerfect)
          (hEDefined.derivedTensor hFDefined) p) =
      ∑ j ∈ Finset.range (p + 1),
        p.choose j •
          (ChernClass.homogeneous δ π j
              (newtonClass δ π classes E hEPerfect hEDefined j) *
            ChernClass.homogeneous δ π (p - j)
              (newtonClass δ π classes F hFPerfect hFDefined (p - j))) := sorry

end AlgebraicGeometry.ChernClass.Derived
