/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_6_9_Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 71.6.9: Let S be a scheme. Let f : X' ⟶ X be a morphism of algebraic
spaces over S. Let Z ⊂ X be a locally principal closed subspace. Then the inverse
image f⁻¹(Z) is a locally principal closed subspace of X'. -/
@[stacks 083X] #check
  (IsLocallyPrincipalClosedSubspace.inverseImageι :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X)
      [IsLocallyPrincipalClosedSubspace i],
      IsLocallyPrincipalClosedSubspace (inverseImageι f i))
