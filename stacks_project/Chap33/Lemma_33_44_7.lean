/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Tensor

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

universe u

/- Lemma 33.44.7: for a proper scheme of dimension at most one over a field, the degree of the
tensor product of finite locally free modules is the rank-weighted sum of their degrees. -/
@[stacks 0AYX] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_tensor_eq_rank_mul_curveDegree_add_rank_mul_curveDegree :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1)
      (ℰ : X.Modules) (rE : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank rE ℰ]
      (𝒱 : X.Modules) (rV : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank rV 𝒱],
      Scheme.Modules.curveDegree f hdim (ℰ ⊗ 𝒱 : X.Modules) (rE * rV) =
        (rE : ℤ) * Scheme.Modules.curveDegree f hdim 𝒱 rV +
          (rV : ℤ) * Scheme.Modules.curveDegree f hdim ℰ rE)
