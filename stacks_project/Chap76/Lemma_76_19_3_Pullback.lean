/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth

/-!
# Base change of formally smooth morphisms of algebraic spaces

Formally smooth morphisms of algebraic spaces are stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Formally smooth morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallySmooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- The base-change projection `pullback.snd f g` of a formally smooth
morphism `f : X ⟶ Y` is formally smooth. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
