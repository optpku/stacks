/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Universally injective morphisms of algebraic spaces

A morphism of algebraic spaces is universally injective when every base change
induces an injective map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism property of inducing an injective map on underlying point spaces. -/
def pointsInjective {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} (f : X ⟶ Y) ↦ Function.Injective (Points.map f)

/-- A morphism has the `pointsInjective` property if and only if the induced map
on points is injective. -/
theorem pointsInjective_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pointsInjective f ↔ Function.Injective (Points.map f) :=
  sorry

/-- A morphism of algebraic spaces is universally injective if every base change
induces an injective map on underlying point spaces. -/
@[mk_iff]
class UniversallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` induces an injective map on points. -/
  universally_injective : universally pointsInjective f

namespace UniversallyInjective

/-- The identity morphism of an algebraic space is universally injective. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversallyInjective (𝟙 X) :=
  sorry

/-- A universally injective morphism has the `universally pointsInjective`
morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyInjective f] : universally pointsInjective f :=
  sorry

/-- A morphism is universally injective as soon as every base change induces an
injective map on points. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : universally pointsInjective f) : UniversallyInjective f :=
  sorry

/-- A universally injective morphism induces an injective map on points. -/
theorem map_injective {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyInjective f] : Function.Injective (Points.map f) :=
  sorry

/-- Universally injective morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversallyInjective g) :
    UniversallyInjective g' :=
  sorry

/-- The base-change projection `pullback.snd f g : Z ×_Y X ⟶ Z` of a universally
injective morphism `f : X ⟶ Y` is universally injective. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversallyInjective f) (g : Z ⟶ Y) [HasPullback f g] :
    UniversallyInjective (pullback.snd f g) :=
  sorry

end UniversallyInjective

/-- A morphism of algebraic spaces is universally injective if and only if every
base change, expressed by an `IsPullback` square, induces an injective map on
points. -/
theorem universallyInjective_iff_injective_of_isPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniversallyInjective f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Function.Injective (Points.map pZ) :=
  sorry

/-- Typeclass form of base-change stability for a universally injective morphism
along a morphism for which the pullback exists. -/
instance universallyInjective_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyInjective f] [HasPullback f g] :
    UniversallyInjective (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
