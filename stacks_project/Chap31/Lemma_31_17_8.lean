/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Reduction
import StacksCheckRecall

/-!
# Lemma 31.17.8

Prime-power norms for reduction morphisms.

@stack 0BDZ
-/

@[expose] public section

/- Lemma 31.17.8: Let `X` be a Noetherian scheme in prime characteristic `p`.
Then the reduction morphism of `X` admits a norm of degree `p ^ e` for some `e > 0`. -/
@[stacks 0BDZ] #check
  (AlgebraicGeometry.Scheme.exists_norm_reduction :
    ∀ (X : AlgebraicGeometry.Scheme) (p : ℕ) [AlgebraicGeometry.IsNoetherian X]
      [Fact p.Prime] [AlgebraicGeometry.Scheme.IsCharP X p],
      ∃ e : ℕ, 0 < e ∧
        ∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm
          (AlgebraicGeometry.Scheme.reductionι X),
          AlgebraicGeometry.Scheme.IsFiniteMorphismNorm
            (AlgebraicGeometry.Scheme.reductionι X) (p ^ e) N)
