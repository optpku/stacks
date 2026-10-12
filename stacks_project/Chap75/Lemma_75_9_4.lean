/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_9_4_Induction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.9.4: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `B ⊂ Ob(X_spaces,étale)`. Let `P` be a property of the
elements of `B`. Assume that every `W ∈ B` is quasi-compact and quasi-separated, if
`W ∈ B` and `U ⊂ W` is quasi-compact open then `U ∈ B`, if `V` is an affine object of
`X_spaces,étale` then `V ∈ B` and `P` holds for `V`, and for every elementary
distinguished square `(U ⊂ W, f : V ⟶ W)` such that `W ∈ B`, `U` is quasi-compact,
`V` is affine, and `P` holds for `U`, `V`, and `U ×_W V`, then `P` holds for `W`.
Then `P` holds for every `W ∈ B`. -/
@[stacks 08GQ] #check
  (@AlgebraicGeometry.AlgebraicSpace.qcqsSpacesEtale_induction_mem :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (B : Set (spacesEtaleSite X)) (P : spacesEtaleSite X → Prop),
    (∀ W ∈ B, IsQuasiCompact W.left) →
    (∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left) →
    (∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B) →
    (∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) →
    (∀ (V : spacesEtaleSite X) [IsAffine V.left], P V) →
    (∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      W ∈ B → P U → P V → P (spacesEtaleSite.fiber j f) → P W) →
    ∀ (W : spacesEtaleSite X), W ∈ B → P W)
