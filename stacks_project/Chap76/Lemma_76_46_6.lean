/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_46_6_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.46.6: if `f : X ⟶ Y` is a morphism of algebraic spaces
pseudo-coherent over a base algebraic space `B`, then `f` is
pseudo-coherent. -/
@[stacks 06BW] #check
  (PseudoCoherent.of_comp :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B)
      [PseudoCoherent g] [PseudoCoherent (f ≫ g)],
      PseudoCoherent f)
