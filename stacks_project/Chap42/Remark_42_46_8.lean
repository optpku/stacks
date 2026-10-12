/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import stacks_project.Chap42.Example_42_43_6_NewtonPolynomial

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- Remark 42.46.8 (1): the positive Newton classes of a perfect derived module satisfy
the usual integral recurrence in its Chern classes. -/
@[stacks 0FAD]
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

/-- Remark 42.46.8 (2): `P₁(E) = c₁(E)` in the total nonnegative
Chow-cohomology ring. -/
@[stacks 0FAD]
theorem newtonClass_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 1 (newtonClass δ π classes E hPerfect hDefined 1) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) := sorry

/-- Remark 42.46.8 (3): `P₂(E) = c₁(E) ^ 2 - 2 • c₂(E)` in the total
nonnegative Chow-cohomology ring. -/
@[stacks 0FAD]
theorem newtonClass_two
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    ChernClass.homogeneous δ π 2 (newtonClass δ π classes E hPerfect hDefined 2) =
      ChernClass.homogeneous δ π 1 (totalClass δ π classes E hPerfect hDefined 1) ^ 2 -
        2 • ChernClass.homogeneous δ π 2
          (totalClass δ π classes E hPerfect hDefined 2) := sorry

/-- Remark 42.46.8 (4): `P₃(E) = c₁(E) ^ 3 - 3 • (c₁(E) * c₂(E)) + 3 • c₃(E)`
in the total nonnegative Chow-cohomology ring. -/
@[stacks 0FAD]
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

/-- Remark 42.46.8 (5): `P₄(E)` is the usual fourth Newton polynomial in the Chern
classes, in the total nonnegative Chow-cohomology ring. -/
@[stacks 0FAD]
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

/-- Remark 42.46.8 (6): the degree-`p` Chern character is the rationalized Newton
class divided by `p!`. -/
@[stacks 0FAD]
theorem character_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (p : ℕ) :
    character δ π classes E hPerfect hDefined p =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined p)
        ((p.factorial : ℚ)⁻¹) := sorry

/-- Remark 42.46.8 (7): in degree zero the Chern character is the rationalized
Newton class, which records the virtual rank. -/
@[stacks 0FAD]
theorem character_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    character δ π classes E hPerfect hDefined 0 =
      TensorProduct.tmul ℤ (newtonClass δ π classes E hPerfect hDefined 0) 1 := sorry

end AlgebraicGeometry.ChernClass.Derived

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- Remark 42.46.8 (8): the augmented degree-zero Newton polynomial is not obtained
from a polynomial in the positive Chern variables, so these variables do not recover rank. -/
@[stacks 0FAD]
theorem augmented_zero_not_mem_rename_succ :
    augmented 0 ∉ Set.range
      (MvPolynomial.rename Nat.succ : MvPolynomial ℕ ℤ → MvPolynomial ℕ ℤ) := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
