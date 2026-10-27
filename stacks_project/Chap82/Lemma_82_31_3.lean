/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernTensor
import StacksCheckRecall

/-!
# Chern classes of tensor products of finite locally free modules

In the good setup of Situation 82.2.1, the first two Chern classes of a tensor
product of finite locally free modules of constant ranks are the rank-weighted
polynomials in `A^*(X)` coming from `c(E ⊗ F) = ∏_{i,j} (1 + x_i + y_j)`.

Local erratum for 0ESE, approved under standing operator review: clause (1)
is unchanged. Clause (2) retains the corrected 0FA6 expansion already present
in this Lean source; the original source display has incorrect coefficients.
For rank-one bundles on the projective plane the printed right side is `H²`,
while the second Chern class of their tensor product is zero. The splitting
proof's final product is the Chern class of `E ⊗ F`, not of `F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open scoped MonoidalCategory

noncomputable section

universe u

/- Lemma 82.31.3 (1): For finite locally free modules `E` and `F` of ranks
`r` and `s` in Situation 82.2.1, `c₁(E ⊗ F) = r c₁(F) + s c₁(E)`.
This clause is unchanged by the approved local erratum to clause (2). -/
@[stacks 0ESE] #check (AlgebraicGeometry.AlgebraicSpace.ChernClass.tensor_one :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F],
    OperationalChow.homogeneous δ f 1 (chernClass δ f (E ⊗ F) 1) =
      (r : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) +
        (s : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 1 (chernClass δ f E 1))

/- Lemma 82.31.3 (2): The approved local erratum replaces the printed second
formula by the integral expansion from the roots `xᵢ + yⱼ`, with coefficients
`r`, `s`, `Nat.choose r 2`, `(r : ℤ) * (s : ℤ) - 1`, and `Nat.choose s 2`.
The original display is false for rank-one bundles on the projective plane. -/
@[stacks 0ESE] #check (AlgebraicGeometry.AlgebraicSpace.ChernClass.tensor_two :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F],
    OperationalChow.homogeneous δ f 2 (chernClass δ f (E ⊗ F) 2) =
      (r : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 2 (chernClass δ f F 2) +
        (s : OperationalChow.ring δ f) * OperationalChow.homogeneous δ f 2 (chernClass δ f E 2) +
        (Nat.choose r 2 : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) ^ 2 +
        (((r : ℤ) * (s : ℤ) - 1 : ℤ) : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f F 1) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f E 1) +
        (Nat.choose s 2 : OperationalChow.ring δ f) *
          OperationalChow.homogeneous δ f 1 (chernClass δ f E 1) ^ 2)

/- The first Chern tensor formula in operational degree one. -/
#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.tensor_one_degree :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F],
    OperationalChow.Graded.ofOperational δ f (chernClass δ f (E ⊗ F) 1) =
      r • OperationalChow.Graded.ofOperational δ f (chernClass δ f F 1) +
        s • OperationalChow.Graded.ofOperational δ f (chernClass δ f E 1))

/- The first Chern tensor formula acting on every good test space. -/
#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.tensor_one_cap :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    (chernClass δ f (E ⊗ F) 1).cap g k =
      r • (chernClass δ f F 1).cap g k +
        s • (chernClass δ f E 1).cap g k)
