module

public import Mathlib.CategoryTheory.CatCommSq
public import stacks_project.Chap84.Lemma_84_6_4_Comparison

/-!
# Lemma 84.6.4

The printed formula for `a_Y` has an `X` subscript typo; the well-typed
composite uses `π_Y ∘ ε_Y` on the `Y` side.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

/-- Lemma 84.6.4 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the big fppf and big étale morphisms of topoi commute with the
identity-on-objects comparisons `epsilon X` and `epsilon Y`. -/
@[stacks 0DGI]
theorem bigEtaleCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Big.morphismOfTopoi f).pushforward
      (epsilon X).pushforward
      (epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward) := sorry

/-- Lemma 84.6.4 (2): after composing `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`
(the printed formula `a_Y = π_X ∘ ε_X` is an `X`-subscript typo), the resulting
direct-image square with `f_small` commutes. -/
@[stacks 0DGI]
theorem smallEtaleCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Big.morphismOfTopoi f).pushforward
      (Etale.SmallToBig.fppfComparison X).pushforward
      (Etale.SmallToBig.fppfComparison Y).pushforward
      (Etale.SmallToBig.smallMorphism f).pushforward) := sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf

end

end
