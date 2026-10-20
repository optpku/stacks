module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- The positive Newton classes of a perfect derived module with defined Chern classes satisfy
the integral Newton recurrence in its Chern classes. -/
theorem newtonClass_succ
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (n : ℕ) :
    ChernClass.homogeneous δ π (n + 1)
        (newtonClass δ π classes E hPerfect hDefined (n + 1)) =
      (∑ j ∈ Finset.range n, ((-1 : ℤ) ^ j) •
        (ChernClass.homogeneous δ π (j + 1)
            (totalClass δ π classes E hPerfect hDefined (j + 1)) *
          ChernClass.homogeneous δ π (n - j)
            (newtonClass δ π classes E hPerfect hDefined (n - j)))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) •
          ChernClass.homogeneous δ π (n + 1)
            (totalClass δ π classes E hPerfect hDefined (n + 1))) := sorry

/-- The first Newton class of a perfect derived module with defined Chern classes equals its
first Chern class in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 1 (newtonClass δ π classes E hPerfect hDefined 1) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) := sorry

/-- The second Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 2 - 2 • c₂(E)` in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_two
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 2 (newtonClass δ π classes E hPerfect hDefined 2) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 2 -
        2 • ChernClass.homogeneous δ π 2
          (totalClass δ π classes E hPerfect hDefined 2) := sorry

/-- The third Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 3 - 3 • (c₁(E) * c₂(E)) + 3 • c₃(E)` in the total nonnegative
Chow-cohomology ring. -/
theorem newtonClass_three
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 3 (newtonClass δ π classes E hPerfect hDefined 3) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 3 -
        3 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2)) +
        3 • ChernClass.homogeneous δ π 3
          (totalClass δ π classes E hPerfect hDefined 3) := sorry

/-- The fourth Newton class of a perfect derived module with defined Chern classes is
`c₁(E) ^ 4 - 4 • (c₁(E) ^ 2 * c₂(E)) + 4 • (c₁(E) * c₃(E)) +
2 • c₂(E) ^ 2 - 4 • c₄(E)` in the total nonnegative Chow-cohomology ring. -/
theorem newtonClass_four
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 4 (newtonClass δ π classes E hPerfect hDefined 4) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 4 -
        4 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) ^ 2 *
          ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2)) +
        4 • (ChernClass.homogeneous δ π 1
            (totalClass δ π classes E hPerfect hDefined 1) *
          ChernClass.homogeneous δ π 3
            (totalClass δ π classes E hPerfect hDefined 3)) +
        2 • ChernClass.homogeneous δ π 2
            (totalClass δ π classes E hPerfect hDefined 2) ^ 2 -
        4 • ChernClass.homogeneous δ π 4
          (totalClass δ π classes E hPerfect hDefined 4) := sorry

/-- The degree-`p` Chern character of a perfect derived module with defined Chern classes is
its rationalized Newton class divided by `p!`. -/
theorem character_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (p : ℕ) :
    character δ π classes E hPerfect hDefined p =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined p)
        ((p.factorial : ℚ)⁻¹) := sorry

/-- The degree-zero Chern character of a perfect derived module with defined Chern classes is
its rationalized degree-zero Newton class, which records the virtual rank. -/
theorem character_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    character δ π classes E hPerfect hDefined 0 =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined 0) 1 := sorry

end AlgebraicGeometry.ChernClass.Derived
