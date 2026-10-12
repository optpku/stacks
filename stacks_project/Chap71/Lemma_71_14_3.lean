/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Lemma 71.14.3

Relative ampleness of an invertible module on an algebraic space is stable
under base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pulling a relatively ample module back around a cartesian square of algebraic
spaces preserves relative ampleness. -/
theorem RelativelyAmple.of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {L : X.Modules} (sq : IsPullback g' f' f g)
    (hL : RelativelyAmple f L) :
    RelativelyAmple f' ((Modules.pullback g').obj L) :=
  sorry

/-- Lemma 71.14.3: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, and let `L` be an invertible `𝒪_X`-module. If `L` is `f`-ample,
then after any base change `g : Y' ⟶ Y` the pullback of `L` to `X ×_Y Y'` is
ample over `Y'`. -/
@[stacks 0D33, instance]
instance RelativelyAmple.pullback {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (L : X.Modules) [RelativelyAmple f L] :
    RelativelyAmple (pullback.snd f g)
      ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
