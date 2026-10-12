/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_9_3_Induction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.9.3: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `P` be a property of the quasi-compact and
quasi-separated objects of `X_spaces,étale`. Assume that `P` holds for every affine
object of `X_spaces,étale`, and that for every elementary distinguished square
`(U ⊂ W, f : V ⟶ W)` such that `W` is a quasi-compact and quasi-separated object of
`X_spaces,étale`, `U` is quasi-compact, `V` is affine, and `P` holds for `U`, `V`, and
`U ×_W V`, then `P` holds for `W`. Then `P` holds for every quasi-compact and
quasi-separated object of `X_spaces,étale`, and in particular for `X`. -/
@[stacks 08GP] #check
  (@AlgebraicGeometry.AlgebraicSpace.qcqsSpacesEtale_induction :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (P : spacesEtaleSite X → Prop),
    (∀ (W : spacesEtaleSite X) [IsAffine W.left], P W) →
    (∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W) →
    ∀ (W : spacesEtaleSite X) [IsQuasiCompact W.left]
      [IsAbsolutelyQuasiSeparated W.left], P W)

#check AlgebraicGeometry.AlgebraicSpace.qcqsSpacesEtale_induction_self
