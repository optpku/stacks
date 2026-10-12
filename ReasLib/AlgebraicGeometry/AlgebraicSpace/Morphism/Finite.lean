/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Integral and finite morphisms of algebraic spaces

A morphism of algebraic spaces is integral, respectively finite, when every
base change along an affine scheme is representable by an affine scheme
integral, respectively finite, over that scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A base change of `f` along `g : yoneda.obj Z ⟶ Y.functorOfPoints` is
representable by an affine scheme integral over `Z`. -/
def isAffineIntegralOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints) : Prop :=
  ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
    IsPullback fst (yoneda.map snd) f g ∧
      IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left

/-- The predicate `isAffineIntegralOver f g` asserts the existence of an affine
scheme representing the pullback of `f` along `g`, with integral projection. -/
theorem isAffineIntegralOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints) :
    isAffineIntegralOver f g ↔
      ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
        IsPullback fst (yoneda.map snd) f g ∧
          IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left :=
  sorry

namespace isAffineIntegralOver

/-- An `isAffineIntegralOver` witness is a represented pullback by an affine
scheme integral over the test object. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {Z : Over S}
    {g : yoneda.obj Z ⟶ Y.functorOfPoints} (h : isAffineIntegralOver f g) :
    ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
      IsPullback fst (yoneda.map snd) f g ∧
        IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left :=
  sorry

/-- A represented pullback by an affine scheme integral over `Z` witnesses
`isAffineIntegralOver`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hpb : IsPullback fst (yoneda.map snd) f g) (hW : IsAffine W.left)
    (hsnd : AlgebraicGeometry.IsIntegralHom snd.left) :
    isAffineIntegralOver f g :=
  sorry

/-- Any represented pullback witnessing the same base change as an
`isAffineIntegralOver` datum is an affine scheme integral over the test
object. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {Z W : Over S} {g : yoneda.obj Z ⟶ Y.functorOfPoints}
    (h : isAffineIntegralOver f g) (fst : yoneda.obj W ⟶ X.functorOfPoints)
    (snd : W ⟶ Z) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left :=
  sorry

end isAffineIntegralOver

/-- A base change of `f` along `g : yoneda.obj Z ⟶ Y.functorOfPoints` is
representable by an affine scheme finite over `Z`. -/
def isAffineFiniteOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints) : Prop :=
  ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
    IsPullback fst (yoneda.map snd) f g ∧
      IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left

/-- The predicate `isAffineFiniteOver f g` asserts the existence of an affine
scheme representing the pullback of `f` along `g`, with finite projection. -/
theorem isAffineFiniteOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints) :
    isAffineFiniteOver f g ↔
      ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
        IsPullback fst (yoneda.map snd) f g ∧
          IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left :=
  sorry

namespace isAffineFiniteOver

/-- An `isAffineFiniteOver` witness is a represented pullback by an affine
scheme finite over the test object. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {Z : Over S}
    {g : yoneda.obj Z ⟶ Y.functorOfPoints} (h : isAffineFiniteOver f g) :
    ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
      IsPullback fst (yoneda.map snd) f g ∧
        IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left :=
  sorry

/-- A represented pullback by an affine scheme finite over `Z` witnesses
`isAffineFiniteOver`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hpb : IsPullback fst (yoneda.map snd) f g) (hW : IsAffine W.left)
    (hsnd : AlgebraicGeometry.IsFinite snd.left) :
    isAffineFiniteOver f g :=
  sorry

/-- Any represented pullback witnessing the same base change as an
`isAffineFiniteOver` datum is an affine scheme finite over the test object. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {Z W : Over S} {g : yoneda.obj Z ⟶ Y.functorOfPoints}
    (h : isAffineFiniteOver f g) (fst : yoneda.obj W ⟶ X.functorOfPoints)
    (snd : W ⟶ Z) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left :=
  sorry

end isAffineFiniteOver

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is integral if every
base change along an affine scheme is representable by an affine scheme
integral over that scheme. -/
@[mk_iff]
class IsIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- Every base change of `f` along an affine scheme is representable by an
  affine scheme integral over that scheme. -/
  affine_integral {Z : Over S} [IsAffine Z.left]
      (g : yoneda.obj Z ⟶ Y.functorOfPoints) : isAffineIntegralOver f g

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite if every
base change along an affine scheme is representable by an affine scheme
finite over that scheme. -/
@[mk_iff]
class IsFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` along an affine scheme is representable by an
  affine scheme finite over that scheme. -/
  affine_finite {Z : Over S} [IsAffine Z.left]
      (g : yoneda.obj Z ⟶ Y.functorOfPoints) : isAffineFiniteOver f g

namespace IsIntegralHom

/-- The identity morphism of an algebraic space is integral. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : IsIntegralHom (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is integral. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : IsIntegralHom f :=
  sorry

/-- An integral morphism of algebraic spaces has every affine-scheme base
change representable by an affine scheme integral over the test object. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] {Z : Over S} [IsAffine Z.left]
    (g : yoneda.obj Z ⟶ Y.functorOfPoints) :
    ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
      IsPullback fst (yoneda.map snd) f g ∧
        IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left :=
  sorry

/-- A universal affine-scheme integral pullback condition witnesses that a
morphism of algebraic spaces is integral. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} [IsAffine Z.left] (g : yoneda.obj Z ⟶ Y.functorOfPoints),
      isAffineIntegralOver f g) : IsIntegralHom f :=
  sorry

/-- Any represented pullback of an integral morphism along an affine scheme is
an affine scheme integral over that scheme. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] {Z W : Over S} [IsAffine Z.left]
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ AlgebraicGeometry.IsIntegralHom snd.left :=
  sorry

/-- For a representable morphism of algebraic spaces, integrality in the sense
 integrality is equivalent to the representable-morphism property
`(over (@AlgebraicGeometry.IsIntegralHom)).presheaf`. -/
theorem presheaf_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    IsIntegralHom f ↔
      (over (@AlgebraicGeometry.IsIntegralHom :
        MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end IsIntegralHom

namespace IsFinite

/-- The identity morphism of an algebraic space is finite. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : IsFinite (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : IsFinite f :=
  sorry

/-- A finite morphism of algebraic spaces has every affine-scheme base change
representable by an affine scheme finite over the test object. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [IsFinite f]
    {Z : Over S} [IsAffine Z.left] (g : yoneda.obj Z ⟶ Y.functorOfPoints) :
    ∃ (W : Over S) (snd : W ⟶ Z) (fst : yoneda.obj W ⟶ X.functorOfPoints),
      IsPullback fst (yoneda.map snd) f g ∧
        IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left :=
  sorry

/-- A universal affine-scheme finite pullback condition witnesses that a
morphism of algebraic spaces is finite. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} [IsAffine Z.left] (g : yoneda.obj Z ⟶ Y.functorOfPoints),
      isAffineFiniteOver f g) : IsFinite f :=
  sorry

/-- Any represented pullback of a finite morphism along an affine scheme is an
affine scheme finite over that scheme. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsFinite f] {Z W : Over S} [IsAffine Z.left]
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ AlgebraicGeometry.IsFinite snd.left :=
  sorry

/-- For a representable morphism of algebraic spaces, finiteness in the sense
 finiteness is equivalent to the representable-morphism property
`(over (@AlgebraicGeometry.IsFinite)).presheaf`. -/
theorem presheaf_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    IsFinite f ↔
      (over (@AlgebraicGeometry.IsFinite :
        MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end IsFinite

/-- A finite morphism of algebraic spaces is integral. -/
instance (priority := 900) instIsIntegralHom_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f] :
    IsIntegralHom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
