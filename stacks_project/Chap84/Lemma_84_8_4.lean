module

import StacksCheckRecall
public import stacks_project.Chap84.Lemma_84_8_4_Big
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

/-!
# Lemma 84.8.4

A morphism of algebraic spaces over a scheme induces two commutative squares
of topoi comparing the big ph, big étale, and small étale sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Lemma 84.8.4 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the identity comparison `epsilon` from `(Spaces/X)_ph` to
`(Spaces/X)_étale` (and likewise on `Y`) yields a commutative square of topoi
with `Ph.Big.morphismOfTopoi` (`f_big,ph`) and `Etale.Big.morphismOfTopoi`
(`f_big,étale`). -/
@[stacks 0DGW] #check (PhComparison.bigPhEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (PhComparison.epsilon X).pushforward
      (PhComparison.epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward))

/- Lemma 84.8.4 (2): with `toSmallEtale X` playing the role of `a_X = π_X ∘ ε_X`
(and likewise `toSmallEtale Y` for `a_Y = π_Y ∘ ε_Y`), the square of
`Ph.Big.morphismOfTopoi` (`f_big,ph`) with `smallEtaleMorphismOfTopoi`
(`f_small`) commutes. -/
@[stacks 0DGW] #check (PhComparison.phSmallEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (PhComparison.toSmallEtale X).pushforward
      (PhComparison.toSmallEtale Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward))

end

end
