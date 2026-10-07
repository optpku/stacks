module

public import stacks_project.Chap75.Lemma_75_9_6_Induction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.9.6: let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `W ⊂ X` be a quasi-compact
open subspace. Let `P` be a property of quasi-compact open subspaces of
`X`. Assume that `P` holds for `W`, and that for every elementary
distinguished square `(W1 ⊂ W2, f : V ⟶ W2)` such that `W1`, `W2` are
quasi-compact open subspaces of `X`, `W ⊂ W1`, `V` is affine, and `P`
holds for `W1`, then `P` holds for `W2`. Then `P` holds for `X`. -/
@[stacks 09IT] #check
  (@AlgebraicGeometry.AlgebraicSpace.qcqsOpenSubspace_induction_enlarge :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (W : OpenSubspace X) [IsQuasiCompact W.X]
      (P : OpenSubspace X → Prop),
    P W →
    (∀ {W1 W2 : OpenSubspace X} {V : AlgebraicSpace S}
      (j : W1.X ⟶ W2.X) (f : V ⟶ W2.X)
      [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact W1.X] [IsQuasiCompact W2.X] [IsAffine V],
      j ≫ W2.ι = W1.ι → (∃ k : W.X ⟶ W1.X, k ≫ W1.ι = W.ι) →
        P W1 → P W2) →
    P (OpenSubspace.id X))
