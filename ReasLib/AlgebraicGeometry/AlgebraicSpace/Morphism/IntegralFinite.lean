/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Affine tests for representable integral and finite morphisms

A representable morphism of algebraic spaces is integral, respectively finite,
if and only if every base change along an affine scheme is an affine scheme
integral, respectively finite, over that scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine-scheme test for a representable morphism `f` to be integral:
every base change of `f` along a morphism from an affine scheme `Z` is an
affine scheme integral over `Z`. -/
def affineAndIntegralOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) : Prop :=
  ∀ {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints),
    IsAffine Z.left →
      IsAffine (hf.pullback g).left ∧ IsIntegralHom (hf.snd g).left

namespace affineAndIntegralOnAffineSchemes

/-- The affine-scheme integral test applies to a given morphism from an affine
scheme. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndIntegralOnAffineSchemes hf) {Z : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints) (hZ : IsAffine Z.left) :
    IsAffine (hf.pullback g).left ∧ IsIntegralHom (hf.snd g).left := sorry

/-- The affine-scheme integral test holds for every represented pullback square,
not only for the chosen `hf.pullback`. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndIntegralOnAffineSchemes hf) {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hZ : IsAffine Z.left) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ IsIntegralHom snd.left := sorry

end affineAndIntegralOnAffineSchemes

/-- The affine-scheme test for a representable morphism `f` to be finite: every
base change of `f` along a morphism from an affine scheme `Z` is an affine
scheme finite over `Z`. -/
def affineAndFiniteOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) : Prop :=
  ∀ {Z : Over S} (g : yoneda.obj Z ⟶ Y.functorOfPoints),
    IsAffine Z.left → IsAffine (hf.pullback g).left ∧ IsFinite (hf.snd g).left

namespace affineAndFiniteOnAffineSchemes

/-- The affine-scheme finite test applies to a given morphism from an affine
scheme. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndFiniteOnAffineSchemes hf) {Z : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints) (hZ : IsAffine Z.left) :
    IsAffine (hf.pullback g).left ∧ IsFinite (hf.snd g).left := sorry

/-- The affine-scheme finite test holds for every represented pullback square,
not only for the chosen `hf.pullback`. -/
theorem of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {hf : yoneda.relativelyRepresentable f}
    (h : affineAndFiniteOnAffineSchemes hf) {Z W : Over S}
    (g : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z)
    (hZ : IsAffine Z.left) (hpb : IsPullback fst (yoneda.map snd) f g) :
    IsAffine W.left ∧ IsFinite snd.left := sorry

end affineAndFiniteOnAffineSchemes

/-- A representable morphism of algebraic spaces is integral if and only if
every affine scheme base change is affine and integral over the base. -/
theorem integralHom_presheaf_iff_affineAndIntegralOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f ↔
      affineAndIntegralOnAffineSchemes hf := sorry

/-- A representable morphism that is integral satisfies the affine-scheme integral test. -/
theorem affineAndIntegralOnAffineSchemes_of_integralHom_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f) :
    affineAndIntegralOnAffineSchemes hf := sorry

/-- A representable morphism that satisfies the affine-scheme integral test is
integral. -/
theorem integralHom_presheaf_of_affineAndIntegralOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : affineAndIntegralOnAffineSchemes hf) :
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A representable morphism of algebraic spaces is finite if and only if
every affine scheme base change is affine and finite over the base. -/
theorem finite_presheaf_iff_affineAndFiniteOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f ↔
      affineAndFiniteOnAffineSchemes hf := sorry

/-- A representable morphism that is finite satisfies the affine-scheme finite test. -/
theorem affineAndFiniteOnAffineSchemes_of_finite_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f) :
    affineAndFiniteOnAffineSchemes hf := sorry

/-- A representable morphism that satisfies the affine-scheme finite test is
finite. -/
theorem finite_presheaf_of_affineAndFiniteOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : affineAndFiniteOnAffineSchemes hf) :
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f := sorry

end AlgebraicGeometry.AlgebraicSpace
