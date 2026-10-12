/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line.Avoidance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.23.5: the closed points in a nonempty open subset of `ℙ(V)` are swept out by
projective lines through `p` that avoid `B`. -/
@[stacks 0B2T] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line.exists_open_coveredBy_avoiding :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (B : IrreducibleCloseds (ProjectiveSpace.VectorSpace.scheme k V)),
      (2 : ℕ∞) ≤ Order.coheight B →
        ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
          IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
            p ∉ (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
              ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
                ∀ q : ProjectiveSpace.VectorSpace.scheme k V,
                  IsClosed ({q} : Set (ProjectiveSpace.VectorSpace.scheme k V)) → q ∈ U →
                    ∃ ℓ : ProjectiveSpace.VectorSpace.Line k V,
                      p ∈ ℓ.carrier ∧ q ∈ ℓ.carrier ∧
                        ℓ.carrier ∩
                          (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) = ∅)

/- There is a projective line through `p` that avoids `B`. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line.exists_avoiding :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (B : IrreducibleCloseds (ProjectiveSpace.VectorSpace.scheme k V)),
      (2 : ℕ∞) ≤ Order.coheight B →
        ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
          IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
            p ∉ (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
              ∃ ℓ : ProjectiveSpace.VectorSpace.Line k V,
                p ∈ ℓ.carrier ∧
                  ℓ.carrier ∩
                    (B : Set (ProjectiveSpace.VectorSpace.scheme k V)) = ∅)
