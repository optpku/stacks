module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Definition_75_9_1_Square

/-!
# Enlarge induction on quasi-compact open subspaces

A property of quasi-compact open subspaces of a quasi-compact
quasi-separated algebraic space that holds for a given quasi-compact
open subspace `W` and is preserved by enlarging along elementary
distinguished squares with affine `V` and `W ⊂ W1` holds for the whole
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property of quasi-compact open subspaces of a quasi-compact
quasi-separated algebraic space `X` that holds for a given quasi-compact
open subspace `W` and is preserved when enlarging `W1` to `W2` along an
elementary distinguished square `(W1 ⊂ W2, f : V ⟶ W2)` with `W ⊂ W1`,
`W1` and `W2` quasi-compact open in `X`, and `V` affine, holds for `X`. -/
theorem qcqsOpenSubspace_induction_enlarge {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (W : OpenSubspace X) [IsQuasiCompact W.X] (P : OpenSubspace X → Prop)
    (hW : P W)
    (h_square : ∀ {W1 W2 : OpenSubspace X} {V : AlgebraicSpace S}
      (j : W1.X ⟶ W2.X) (f : V ⟶ W2.X)
      [IsElementaryDistinguishedSquare j f]
      [IsQuasiCompact W1.X] [IsQuasiCompact W2.X] [IsAffine V],
      j ≫ W2.ι = W1.ι → (∃ k : W.X ⟶ W1.X, k ≫ W1.ι = W.ι) →
        P W1 → P W2) :
    P (OpenSubspace.id X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
