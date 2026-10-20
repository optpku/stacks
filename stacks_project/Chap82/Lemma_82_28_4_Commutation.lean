/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Center
public import stacks_project.Chap82.Lemma_82_28_1_Chern

/-!
# Commutation of constant-rank Chern identity classes

In Situation 82.2.1, each identity class `c_j(E)` of a finite locally free
module of constant rank on a good algebraic space `X / B` commutes with every
homogeneous class in `A^*(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- The identity class `ConstantRankChern.degree f δ E q j hj` commutes in
`A^*(X)` with every homogeneous class `c ∈ A^p(X)`. -/
theorem chernClass_comm (j : ℕ) (hj : j ≤ q + 1) (p : ℤ) (c : degree δ f p) :
    homogeneous δ f j (ConstantRankChern.degree f δ E q j hj) * homogeneous δ f p c =
      homogeneous δ f p c * homogeneous δ f j (ConstantRankChern.degree f δ E q j hj) :=
  sorry

/-- Capping with `ConstantRankChern.degree f δ E q j hj` commutes with capping
by a homogeneous identity class, after reindexing along
`k - j - p = k - p - j`. -/
theorem chernClass_cap_comm (j : ℕ) (hj : j ≤ q + 1)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (p : ℤ) (c : degree δ f p) (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (ConstantRankChern.degree f δ E q j hj).cap g (k - p) (c.cap g k α) =
      castChowGroup δ (g ≫ f) (sub_right_comm k (j : ℤ) p)
        (c.cap g (k - j) ((ConstantRankChern.degree f δ E q j hj).cap g k α)) :=
  sorry

/-- The identity class `homogeneous δ f j (ConstantRankChern.degree f δ E q j hj)`
lies in the center of the Chow cohomology ring `A^*(X)`. -/
theorem chernClass_mem_center (j : ℕ) (hj : j ≤ q + 1) :
    homogeneous δ f j (ConstantRankChern.degree f δ E q j hj) ∈ Set.center (ring δ f) :=
  sorry

/-- Capping with Chern identity classes of two finite locally free modules
commutes on Chow groups, after reindexing along `k - i - j = k - j - i`. -/
theorem chernClasses_cap_comm (F : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (s + 1) F]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i : ℕ) (hi : i ≤ q + 1) (j : ℕ) (hj : j ≤ s + 1)
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (ConstantRankChern.degree f δ E q i hi).cap g (k - j)
        ((ConstantRankChern.degree f δ F s j hj).cap g k α) =
      castChowGroup δ (g ≫ f) (sub_right_comm k (i : ℤ) (j : ℤ))
        ((ConstantRankChern.degree f δ F s j hj).cap g (k - i)
          ((ConstantRankChern.degree f δ E q i hi).cap g k α)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
