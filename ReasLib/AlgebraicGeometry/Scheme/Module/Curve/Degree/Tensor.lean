/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Components
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Degrees and Euler characteristics of tensor products on proper curves

This file relates the Euler characteristic of a coherent module tensored with a finite locally
free module to the degree of the latter and the generic fiber rank of the former. It also records
the degree of a tensor product of two finite locally free modules on a proper scheme of dimension
at most one.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On a proper curve over a field, the Euler characteristic of a coherent module tensored with
a finite locally free module is determined by the latter's degree and rank and the former's
generic fiber rank. -/
theorem eulerCharacteristic_tensor_eq_genericRank_mul_curveDegree_add_rank_mul
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    (ℰ : X.left.Modules) (n : ℕ) [IsFiniteLocallyFreeOfRank n ℰ]
    (ℱ : X.left.Modules) [ℱ.IsCoherent] :
    let _ : IsLocallyNoetherian X.left :=
      LocallyOfFiniteType.isLocallyNoetherian X.hom
    let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
    let _ : (ℰ ⊗ ℱ : X.left.Modules).IsCoherent := isCoherent_tensor
    Scheme.Hom.eulerCharacteristic X.hom (ℰ ⊗ ℱ) =
      (fiberFinrank ℱ (genericPoint X.left) : ℤ) *
          curveDegree X.hom (AlgebraicGeometry.topologicalKrullDim_eq_one X).le ℰ n +
        (n : ℤ) * Scheme.Hom.eulerCharacteristic X.hom ℱ := sorry

/-- The degree of the tensor product of finite locally free modules of ranks `rE` and `rV` on a
proper scheme of dimension at most one is `rE` times the degree of the second module plus `rV`
times the degree of the first. -/
@[stacks 0AYX]
theorem curveDegree_tensor_eq_rank_mul_curveDegree_add_rank_mul_curveDegree
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (ℰ : X.Modules) (rE : ℕ) [IsFiniteLocallyFreeOfRank rE ℰ]
    (𝒱 : X.Modules) (rV : ℕ) [IsFiniteLocallyFreeOfRank rV 𝒱] :
    curveDegree f hdim (ℰ ⊗ 𝒱 : X.Modules) (rE * rV) =
      (rE : ℤ) * curveDegree f hdim 𝒱 rV +
        (rV : ℤ) * curveDegree f hdim ℰ rE := sorry

end AlgebraicGeometry.Scheme.Modules
