module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Polarized.HilbertEmbedding

/-!
# Lemma 108.11.3

A subset of `|Polarized|` whose points are represented by polarized pairs of
Hilbert polynomial `P` that embed as closed subschemes of `P^n` over a field is
Noetherian, hence quasi-compact.
-/

/- Lemma 108.11.3: the locus with fixed Hilbert polynomial and projective
embedding dimension has Noetherian subsets. -/
@[stacks 0E96] #check
  (AlgebraicGeometry.Polarized.noetherianSpace_hilbertEmbedded :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {P : ℤ → ℤ}, IsNumericalPolynomial P →
      ∀ T : Set (AlgebraicGeometry.AlgebraicStack.Points
        AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ),
        T ⊆ AlgebraicGeometry.Polarized.hilbertEmbeddedSet n P →
          TopologicalSpace.NoetherianSpace T)

#check (AlgebraicGeometry.Polarized.isCompact_hilbertEmbedded :
  ∀ {n : ℕ}, 1 ≤ n → ∀ {P : ℤ → ℤ}, IsNumericalPolynomial P →
    ∀ T : Set (AlgebraicGeometry.AlgebraicStack.Points
      AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ),
      T ⊆ AlgebraicGeometry.Polarized.hilbertEmbeddedSet n P → CompactSpace T)
