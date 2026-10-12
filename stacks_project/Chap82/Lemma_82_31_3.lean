/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.«82_29_1_1_Tensor»

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
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.31.3 (1): In Situation 82.2.1 let `X / B` be good. Let `E` and `F`
be finite locally free `𝒪_X`-modules of ranks `r` and `s`. Then
`c₁(E ⊗ F) = r c₁(F) + s c₁(E)` in `A^*(X)`.
This clause is unchanged by the approved local erratum to clause (2). -/
@[stacks 0ESE]
theorem tensor_one {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    homogeneous δ f 1 (chernClass δ f (E ⊗ F) 1) =
      (r : ring δ f) * homogeneous δ f 1 (chernClass δ f F 1) +
        (s : ring δ f) * homogeneous δ f 1 (chernClass δ f E 1) := sorry

/-- Lemma 82.31.3 (2): Local erratum for 0ESE, approved under standing operator
review. This retains the existing corrected 0FA6 expansion, obtained from the
line-factor roots `xᵢ + yⱼ`; the original printed display is false for rank-one
bundles. All original hypotheses and binders are retained; clause (1) is unchanged. -/
@[stacks 0ESE]
theorem tensor_two {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    homogeneous δ f 2 (chernClass δ f (E ⊗ F) 2) =
      (r : ring δ f) * homogeneous δ f 2 (chernClass δ f F 2) +
        (s : ring δ f) * homogeneous δ f 2 (chernClass δ f E 2) +
        (Nat.choose r 2 : ring δ f) *
          homogeneous δ f 1 (chernClass δ f F 1) ^ 2 +
        (((r : ℤ) * (s : ℤ) - 1 : ℤ) : ring δ f) *
          homogeneous δ f 1 (chernClass δ f F 1) *
          homogeneous δ f 1 (chernClass δ f E 1) +
        (Nat.choose s 2 : ring δ f) *
          homogeneous δ f 1 (chernClass δ f E 1) ^ 2 := sorry

/-- The first Chern class of a tensor product of finite locally free modules of
ranks `r` and `s` is the rank-weighted sum in `A^1(X)`. -/
theorem tensor_one_degree {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F] :
    chernClass δ f (E ⊗ F) 1 =
      r • chernClass δ f F 1 + s • chernClass δ f E 1 := sorry

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

end AlgebraicGeometry.AlgebraicSpace.ChernClass
