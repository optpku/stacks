/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Tensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- For a finite locally free module `E` of rank `r` and an invertible module `L`,
the degree-`i` Chern class of `E ⊗ L` is the corresponding binomial sum in
nonnegative operational Chow cohomology. -/
theorem chernClass_tensor_invertible
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (E L : X.Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    [Scheme.Modules.Invertible L] :
    let hE : E.IsFiniteLocallyFree :=
      Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r E
    let hLRank : L.IsFiniteLocallyFreeOfRank 1 :=
      Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible L
    let hL : L.IsFiniteLocallyFree :=
      @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank X 1 L hLRank
    let hTensor : (E ⊗ L : X.Modules).IsFiniteLocallyFree :=
      @SheafOfModules.IsFiniteLocallyFree.tensor _ _ _ _ _ _ _ _ _ E L hE hL
    ChernClass.homogeneous δ p i
        (@ChernClass.chernClass S X inferInstance δ inferInstance p inferInstance
          (E ⊗ L) hTensor i) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p (i - j)
            (@ChernClass.chernClass S X inferInstance δ inferInstance p inferInstance
              E hE (i - j)) *
            ChernClass.homogeneous δ p 1
              (ChowCohomology.firstChernClass δ p L) ^ j := sorry

namespace ChernClass.Theory

/-- The first Chern class of the tensor product of finite locally free modules of
constant ranks `r` and `s` is the rank-weighted sum of their first Chern classes. -/
theorem component_tensor_one
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E F : X.Modules) (r s : ℕ)
    [E.IsFiniteLocallyFreeOfRank r] [F.IsFiniteLocallyFreeOfRank s] :
    ChernClass.homogeneous δ p 1 (classes.component (E ⊗ F) 1) =
      (r : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 1 (classes.component F 1) +
        (s : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 1 (classes.component E 1) := sorry

/-- The second Chern class of the tensor product of finite locally free modules
of constant ranks `r` and `s` is the rank-weighted quadratic expansion in their
first two Chern classes. -/
theorem component_tensor_two
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E F : X.Modules) (r s : ℕ)
    [E.IsFiniteLocallyFreeOfRank r] [F.IsFiniteLocallyFreeOfRank s] :
    ChernClass.homogeneous δ p 2 (classes.component (E ⊗ F) 2) =
      (r : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 2 (classes.component F 2) +
        (s : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 2 (classes.component E 2) +
        (Nat.choose r 2 : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 1 (classes.component F 1) ^ 2 +
        (((r : ℤ) * (s : ℤ) - 1 : ℤ) : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 1 (classes.component F 1) *
          ChernClass.homogeneous δ p 1 (classes.component E 1) +
        (Nat.choose s 2 : ChowCohomology.Nonnegative.ring δ p) *
          ChernClass.homogeneous δ p 1 (classes.component E 1) ^ 2 := sorry

end ChernClass.Theory

end AlgebraicGeometry
