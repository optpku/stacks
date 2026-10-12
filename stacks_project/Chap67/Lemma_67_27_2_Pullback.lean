/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite

/-!
# Base change of quasi-finite morphisms of algebraic spaces

Locally quasi-finite morphisms and quasi-finite morphisms of algebraic spaces
are stable under arbitrary base change. This module records the
morphism-level pullback companions for the existing `LocallyQuasiFinite` and
`QuasiFinite` classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyQuasiFinite

/-- Locally quasi-finite morphisms of algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyQuasiFinite g) :
    LocallyQuasiFinite g' := sorry

/-- The base-change projection `pullback.snd f g` of a locally quasi-finite
morphism `f : X ⟶ Y` is locally quasi-finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyQuasiFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

/-- Locally quasi-finite morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyQuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

end LocallyQuasiFinite

/-- Typeclass form of base-change stability for a locally quasi-finite morphism
along a morphism for which the pullback exists. -/
instance locallyQuasiFinite_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyQuasiFinite f] [HasPullback f g] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

namespace QuasiFinite

/-- Quasi-finite morphisms of algebraic spaces are stable under pullback along
an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiFinite g) : QuasiFinite g' := sorry

/-- The base-change projection `pullback.snd f g` of a quasi-finite morphism
`f : X ⟶ Y` is quasi-finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiFinite (pullback.snd f g) := sorry

end QuasiFinite

/-- Typeclass form of base-change stability for a quasi-finite morphism along a
morphism for which the pullback exists. -/
instance quasiFinite_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiFinite f] [HasPullback f g] :
    QuasiFinite (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
