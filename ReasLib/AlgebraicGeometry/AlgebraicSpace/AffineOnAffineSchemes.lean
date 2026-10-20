/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Affine-on-affine-schemes morphisms

This module records the affine-scheme pullback criterion for representable
morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces is affine on affine schemes when every
represented pullback along a morphism from an affine scheme is affine. -/
def isAffineOnAffineSchemes : Prop :=
  ∀ ⦃Z W : Over S⦄ [IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z),
    IsPullback fst (yoneda.map snd) f ξ → IsAffine W.left

/-- The affine-on-affine-schemes predicate has an explicit universal form. -/
theorem isAffineOnAffineSchemes_iff :
    isAffineOnAffineSchemes f ↔
      ∀ (Z W : Over S) [IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y.functorOfPoints)
        (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z),
        IsPullback fst (yoneda.map snd) f ξ → IsAffine W.left :=
  sorry

namespace isAffineOnAffineSchemes

/-- A universal affine-scheme pullback condition implies the
affine-on-affine-schemes predicate. -/
theorem of
    (h : ∀ ⦃Z W : Over S⦄ [IsAffine Z.left] (ξ : yoneda.obj Z ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ Z),
      IsPullback fst (yoneda.map snd) f ξ → IsAffine W.left) :
    isAffineOnAffineSchemes f :=
  sorry

/-- The affine-on-affine-schemes predicate supplies affinity for every
represented pullback along a morphism from an affine scheme. -/
theorem spec (h : isAffineOnAffineSchemes f) {Z W : Over S} [IsAffine Z.left]
    (ξ : yoneda.obj Z ⟶ Y.functorOfPoints) (fst : yoneda.obj W ⟶ X.functorOfPoints)
    (snd : W ⟶ Z) (hP : IsPullback fst (yoneda.map snd) f ξ) :
    IsAffine W.left :=
  sorry

end isAffineOnAffineSchemes

/-- For a relatively representable morphism, the affine-on-affine-schemes
predicate is equivalent to affinity of the chosen represented pullbacks. -/
theorem isAffineOnAffineSchemes_iff_pullback (hf : yoneda.relativelyRepresentable f) :
    isAffineOnAffineSchemes f ↔
      ∀ {Z : Over S} [IsAffine Z.left] (g : yoneda.obj Z ⟶ Y.functorOfPoints),
        IsAffine (hf.pullback g).left :=
  sorry

/-- For a relatively representable morphism, the affine-on-affine-schemes
predicate is equivalent to affinity of the chosen represented pullback maps. -/
theorem isAffineOnAffineSchemes_iff_isAffineHom
    (hf : yoneda.relativelyRepresentable f) :
    isAffineOnAffineSchemes f ↔
      ∀ {Z : Over S} [IsAffine Z.left] (g : yoneda.obj Z ⟶ Y.functorOfPoints),
        IsAffineHom (hf.snd g).left :=
  sorry

/-- A relatively representable morphism is affine in the presheaf sense
exactly when it is affine on affine schemes. -/
theorem isAffineHom_presheaf_iff_isAffineOnAffineSchemes
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f ↔
      isAffineOnAffineSchemes f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
