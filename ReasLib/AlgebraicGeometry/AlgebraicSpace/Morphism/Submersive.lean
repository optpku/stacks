/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuotientMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Submersive morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is submersive when its map on points is a
quotient map for canonical point-space topologies. -/
@[mk_iff]
class Submersive {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is a quotient map for every pair of
  canonical topologies. -/
  isQuotientMap : pointsIsQuotientMap f

namespace Submersive

/-- The identity morphism of an algebraic space is submersive. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Submersive (𝟙 X) := sorry

/-- A submersive morphism induces a quotient map on points for any pair of
canonical topologies. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Submersive f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isQuotientMapOnPoints τX τY f :=
  sorry

/-- A morphism is submersive as soon as it induces a quotient map on canonical
point spaces. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsQuotientMap f) : Submersive f :=
  sorry

end Submersive

/-- A morphism of algebraic spaces is universally submersive when every base
change induces a quotient map on points. -/
@[mk_iff]
class UniversallySubmersive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` induces a quotient map on points. -/
  universally_isQuotientMap : universally pointsIsQuotientMap f

namespace UniversallySubmersive

/-- The identity morphism of an algebraic space is universally submersive. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversallySubmersive (𝟙 X) :=
  sorry

/-- A universally submersive morphism has the `universally pointsIsQuotientMap`
morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallySubmersive f] : universally pointsIsQuotientMap f :=
  sorry

/-- Every base change of a universally submersive morphism, expressed by an
`IsPullback` square, is a submersive morphism. -/
theorem isSubmersive_of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [UniversallySubmersive f] (h : IsPullback pZ pX g f) : Submersive pZ :=
  sorry

/-- Universally submersive morphisms of algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversallySubmersive g) :
    UniversallySubmersive g' :=
  sorry

/-- The base-change projection `pullback.snd f g : Z ×_Y X ⟶ Z` of a universally
submersive morphism `f : X ⟶ Y` is universally submersive. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversallySubmersive f) (g : Z ⟶ Y) [HasPullback f g] :
    UniversallySubmersive (pullback.snd f g) :=
  sorry

end UniversallySubmersive

/-- A universally submersive morphism of algebraic spaces is submersive. -/
instance instSubmersive_of_universallySubmersive {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallySubmersive f] :
    Submersive f :=
  sorry

/-- Pulling back a universally submersive morphism along any morphism for which
the pullback exists gives a universally submersive projection. -/
instance universallySubmersive_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallySubmersive f] [HasPullback f g] :
    UniversallySubmersive (pullback.snd f g) :=
  sorry

/-- A submersive morphism of algebraic spaces is surjective. -/
instance instSurjective_of_submersive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Submersive f] : Surjective f :=
  sorry

/-- A morphism of algebraic spaces is universally submersive if and only if every
base change, expressed by an `IsPullback` square, is a submersive morphism. -/
theorem universallySubmersive_iff_isSubmersive_of_isPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniversallySubmersive f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Submersive pZ :=
  sorry

/-- A representable morphism of algebraic spaces is universally submersive when
tested on represented scheme base changes if and only if every algebraic-space
base change induces a quotient map on canonical point spaces. -/
theorem universallySubmersive_presheaf_iff_universally_pointsIsQuotientMap
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallySubmersive : MorphismProperty Scheme.{u})).presheaf f ↔
      universally pointsIsQuotientMap f :=
  sorry

/-- A representable morphism that is universally submersive on represented
scheme base changes is universally a quotient map on points. -/
theorem universally_pointsIsQuotientMap_of_universallySubmersive_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallySubmersive :
      MorphismProperty Scheme.{u})).presheaf f) :
    universally pointsIsQuotientMap f :=
  (universallySubmersive_presheaf_iff_universally_pointsIsQuotientMap hf).mp h

/-- A representable morphism that is universally a quotient map on points is
universally submersive on represented scheme base changes. -/
theorem universallySubmersive_presheaf_of_universally_pointsIsQuotientMap
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : universally pointsIsQuotientMap f) :
    (over (@AlgebraicGeometry.UniversallySubmersive : MorphismProperty Scheme.{u})).presheaf f :=
  (universallySubmersive_presheaf_iff_universally_pointsIsQuotientMap hf).mpr h

end AlgebraicGeometry.AlgebraicSpace
