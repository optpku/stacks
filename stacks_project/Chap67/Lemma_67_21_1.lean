/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
import StacksCheckRecall

/-!
# Quasi-affine representable morphisms of algebraic spaces

A representable morphism of algebraic spaces is quasi-affine in the sense of
Section 67.3 if and only if every base change along a morphism from an affine
scheme is a quasi-affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 67.21.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is quasi-affine in the sense of
Section 67.3 if and only if for all affine schemes `Z` and morphisms `Z ⟶ Y`
the scheme `X ×_Y Z` is quasi-affine. -/
@[stacks 03WK] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiAffineHom_presheaf_iff_isQuasiAffine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      (hf : yoneda.relativelyRepresentable f),
        (over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f ↔
          ∀ {Z : Over S} [IsAffine Z.left]
            (g : yoneda.obj Z ⟶ Y.functorOfPoints),
            (hf.pullback g).left.IsQuasiAffine)
