/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.CapPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.GradedRing

/-! # Chern classes of tensor products of finite locally free modules -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a good algebraic space `X` over a universally catenary quasi-separated
base `B`, a finite locally free `𝒪_X`-module `E` of rank `r`, and an invertible
`𝒪_X`-module `L`, the identity `c_i(E ⊗ L) = ∑ j, Nat.choose (r + j - i) j •
c_{i-j}(E) * c_1(L)^j` holds as an equality of cap operations on every good
test `g : Y ⟶ X`. -/
theorem chernClass_tensor_invertible {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E L : X.Modules) (r i : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [isInvertibleObject L]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : chowGroup (g ≫ f) δ k) :
    (ChernClass.chernClass δ f (E ⊗ L) i).cap g k α =
      ∑ j ∈ Finset.range (i + 1),
        Nat.choose (r + j - i) j •
          (if hj : j ≤ i then
            (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
              (show (k - (j : ℤ)) - ((i - j : ℕ) : ℤ) = k - (i : ℤ) by
                rw [Nat.cast_sub hj]
                omega)).toAddMonoidHom
              ((ChernClass.chernClass δ f E (i - j)).cap g (k - (j : ℤ))
                (ChowCohomology.powCap (ChernClass.chernClass δ f L 1).cap j g k α))
          else 0) := sorry


namespace ChernClass

/-- The first Chern class of the tensor product of finite locally free modules of
constant ranks `r` and `s` is the rank-weighted sum in the operational Chow ring. -/
theorem tensor_one {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    OperationalChow.homogeneous δ f 1 (chernClass δ f (E ⊗ F) 1) =
      (r : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) +
        (s : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 1 (chernClass δ f E 1) := sorry

/-- The second Chern class of the tensor product of finite locally free modules
of constant ranks `r` and `s` is the integral quadratic expansion in their first
two Chern classes, with mixed coefficient `(r : ℤ) * (s : ℤ) - 1`. -/
theorem tensor_two {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    OperationalChow.homogeneous δ f 2 (chernClass δ f (E ⊗ F) 2) =
      (r : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 2 (chernClass δ f F 2) +
        (s : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 2 (chernClass δ f E 2) +
        (Nat.choose r 2 : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) ^ 2 +
        (((r : ℤ) * (s : ℤ) - 1 : ℤ) : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f E 1) +
        (Nat.choose s 2 : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f E 1) ^ 2 := sorry

/-- The first Chern class of a tensor product of finite locally free modules of
ranks `r` and `s` is the rank-weighted sum of their compatible cap families
in the degree-one operational Chow subgroup. -/
theorem tensor_one_degree {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    OperationalChow.Graded.ofOperational δ f (chernClass δ f (E ⊗ F) 1) =
      r • OperationalChow.Graded.ofOperational δ f (chernClass δ f F 1) +
        s • OperationalChow.Graded.ofOperational δ f (chernClass δ f E 1) := sorry

/-- Capping with `c₁(E ⊗ F)` is the rank-weighted sum of the first Chern caps of
`E` and `F` on every good test `Y ⟶ X`. -/
theorem tensor_one_cap {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f (E ⊗ F) 1).cap g k =
      r • (chernClass δ f F 1).cap g k +
        s • (chernClass δ f E 1).cap g k := sorry

end ChernClass

end AlgebraicGeometry.AlgebraicSpace
