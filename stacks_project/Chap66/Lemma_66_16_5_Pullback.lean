/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Base change of étale morphisms of algebraic spaces

Étale morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Etale` class from Lemma 66.16.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Étale morphisms of algebraic spaces are stable under pullback along an
arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Etale g) : Etale g' := sorry

/-- The base-change projection `pullback.snd f g` of an étale morphism
`f : X ⟶ Y` is étale. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Etale f) (g : Z ⟶ Y) [HasPullback f g] :
    Etale (pullback.snd f g) := sorry

/-- The base-change projection `pullback.fst f g` of an étale morphism
`g : Z ⟶ Y` is étale. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    {g : Z ⟶ Y} (hg : Etale g) [HasPullback f g] :
    Etale (pullback.fst f g) := sorry

/-- Étale morphisms of algebraic spaces over `S` are stable under arbitrary
base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    IsStableUnderBaseChange (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Typeclass form of base-change stability for an étale morphism along a
morphism for which the pullback exists. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale f] [HasPullback f g] :
    Etale (pullback.snd f g) := sorry

/-- Typeclass form of base-change stability for the first projection of a
pullback of an étale morphism. -/
instance instPullbackFst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale g] [HasPullback f g] :
    Etale (pullback.fst f g) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
