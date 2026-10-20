/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Universally injective morphisms of algebraic spaces

Universal injectivity of a morphism of algebraic spaces is defined by
injectivity on points after every base change. Representable morphisms are
universally injective exactly when they are injective on field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism property of inducing an injective map on the point spaces of
algebraic spaces over a scheme. -/
def pointsInjective {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} (f : X ⟶ Y) ↦ Function.Injective (Points.map f)

/-- A morphism has `pointsInjective` precisely when its map on points is
injective. -/
theorem pointsInjective_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pointsInjective f ↔ Function.Injective (Points.map f) :=
  sorry

/-- A morphism of algebraic spaces is universally injective when every base
change induces an injective map on points. -/
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

/-- A universally injective morphism satisfies the universal point-injectivity
morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyInjective f] : universally pointsInjective f :=
  sorry

/-- A morphism is universally injective when it satisfies the universal
point-injectivity morphism property. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : universally pointsInjective f) : UniversallyInjective f :=
  sorry

/-- A universally injective morphism induces an injective map on points. -/
theorem map_injective {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyInjective f] : Function.Injective (Points.map f) :=
  sorry

/-- Universal injectivity descends across an arbitrary cartesian square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversallyInjective g) :
    UniversallyInjective g' :=
  sorry

/-- The second projection from a pullback of a universally injective morphism
is universally injective. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversallyInjective f) (g : Z ⟶ Y) [HasPullback f g] :
    UniversallyInjective (pullback.snd f g) :=
  sorry

end UniversallyInjective

/-- Universal injectivity is equivalent to injectivity on points in every
cartesian base-change square. -/
theorem universallyInjective_iff_injective_of_isPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniversallyInjective f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Function.Injective (Points.map pZ) :=
  sorry

/-- The pullback projection of a universally injective morphism is universally
injective whenever the pullback exists. -/
instance universallyInjective_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyInjective f] [HasPullback f g] :
    UniversallyInjective (pullback.snd f g) :=
  sorry

/-- Universal injectivity of algebraic-space morphisms is stable under base
change. -/
instance universallyInjective_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallyInjective S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- A representable morphism of algebraic spaces over a scheme is universally
injective, as tested on represented scheme pullbacks, if and only if it is
injective on points valued in every field over the base scheme. -/
theorem universallyInjective_iff_injectiveOnFieldPoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})).presheaf f ↔
      injectiveOnFieldPoints f := sorry

end AlgebraicGeometry.AlgebraicSpace
