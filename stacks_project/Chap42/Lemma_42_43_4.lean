/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Tensor

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/- Lemma 42.43.4 (1): For finite locally free modules `E` and `F` of ranks `r` and
`s`, the first Chern class of `E ⊗ F` is `r * c₁(F) + s * c₁(E)`. -/
@[stacks 0FA6] #check
  (AlgebraicGeometry.ChernClass.Theory.component_tensor_one :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : Theory δ p) (E F : X.Modules) (r s : ℕ)
      [E.IsFiniteLocallyFreeOfRank r] [F.IsFiniteLocallyFreeOfRank s],
      ChernClass.homogeneous δ p 1 (classes.component (E ⊗ F) 1) =
        (r : ChowCohomology.Nonnegative.ring δ p) *
            ChernClass.homogeneous δ p 1 (classes.component F 1) +
          (s : ChowCohomology.Nonnegative.ring δ p) *
            ChernClass.homogeneous δ p 1 (classes.component E 1))

/- Lemma 42.43.4 (2): For finite locally free modules `E` and `F` of ranks `r` and
`s`, the second Chern class of `E ⊗ F` has the stated rank-weighted expansion in
the first two Chern classes of `E` and `F`. -/
@[stacks 0FA6] #check
  (AlgebraicGeometry.ChernClass.Theory.component_tensor_two :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : Theory δ p) (E F : X.Modules) (r s : ℕ)
      [E.IsFiniteLocallyFreeOfRank r] [F.IsFiniteLocallyFreeOfRank s],
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
            ChernClass.homogeneous δ p 1 (classes.component E 1) ^ 2)

end AlgebraicGeometry.ChernClass.Theory
