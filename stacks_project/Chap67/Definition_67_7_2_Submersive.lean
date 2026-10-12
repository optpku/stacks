/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_7_1_Quotient

/-!
# Submersive and universally submersive morphisms of algebraic spaces

A morphism of algebraic spaces is submersive when it induces a quotient map on
underlying point spaces, and universally submersive when every base change is
submersive. The canonical topology on `Points` is characterized rather than
constructed, so competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is submersive if the induced map on underlying
point spaces is a quotient map. -/
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

/-- A morphism of algebraic spaces is universally submersive if every base change
induces a quotient map on underlying point spaces. -/
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

/-- Typeclass form of base-change stability for a universally submersive morphism
along a morphism for which the pullback exists. -/
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

end AlgebraicGeometry.AlgebraicSpace
