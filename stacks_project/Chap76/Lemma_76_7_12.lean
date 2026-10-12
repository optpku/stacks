/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_7_12_Comparison
import StacksCheckRecall

/-!
# Base change of the sheaf of differentials of a morphism of algebraic spaces

A cartesian square of algebraic spaces over a scheme `S` makes the Lemma 76.7.6
comparison on relative differentials an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X X' Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable (hpb : IsPullback g' f' f g)

/- Lemma 76.7.12: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` and a
morphism `g : Y' ⟶ Y`, if `X'` is the base change of `X` along `g` with projection
`g' : X' ⟶ X`, then the comparison `(g')^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Lemma 76.7.6 is an
isomorphism. -/
@[stacks 05ZC] #check (comparison_isIso_of_isPullback hpb :
  IsIso (comparison g' g f f' hpb.w))
