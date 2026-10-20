module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FiniteLocallyFree
import StacksCheckRecall

/-!
# Lemma 31.17.6

Canonical norms of finite locally free morphisms of constant rank.

@stack 0BD2
-/

@[expose] public section

/- Lemma 31.17.6: A finite locally free morphism of constant positive rank admits a canonical
norm of that degree, compatible with arbitrary base change. -/
@[stacks 0BD2] #check
  (AlgebraicGeometry.Scheme.exists_norm_of_finiteLocallyFreeOfRank :
    ∀ {X Y : AlgebraicGeometry.Scheme} (π : X ⟶ Y) (d : ℕ)
        [AlgebraicGeometry.IsFiniteLocallyFreeOfRank π d],
      1 ≤ d →
        ∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
          AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π d N ∧
            AlgebraicGeometry.Scheme.FiniteMorphismNorm.IsDeterminant N)
