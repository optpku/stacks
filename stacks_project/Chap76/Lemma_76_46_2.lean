/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_46_2_BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.46.2: A flat base change of a pseudo-coherent morphism is pseudo-coherent. -/
@[stacks 06BS] #check
  (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [HasPullback f g] [PseudoCoherent f] [Flat g],
      PseudoCoherent (pullback.snd f g))
