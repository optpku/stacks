/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
import StacksCheckRecall

/-!
# Lemma 29.11.12

Affine morphisms obtained from affine composites, affine diagonals, and separated targets.

@stack 01SG
-/

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 29.11.12 (1): an affine composite can be cancelled when the second map has affine
diagonal. -/
@[stacks 01SG] #check
  (AlgebraicGeometry.isAffineHom_of_isAffineHom_comp_of_affineDiagonal :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
      [AlgebraicGeometry.IsAffineHom (g ≫ f)]
      [AlgebraicGeometry.IsAffineHom (pullback.diagonal f)],
      AlgebraicGeometry.IsAffineHom g)

/- Lemma 29.11.12 (2): an affine composite can be cancelled when the second map is
separated. -/
@[stacks 01SG] #check
  (AlgebraicGeometry.IsAffineHom.of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
      [AlgebraicGeometry.IsAffineHom (g ≫ f)] [AlgebraicGeometry.IsSeparated f],
      AlgebraicGeometry.IsAffineHom g)

/- Lemma 29.11.12 (3): every morphism from an affine scheme to a scheme with affine
absolute diagonal is affine. -/
@[stacks 01SG] #check
  (AlgebraicGeometry.isAffineHom_of_isAffine_of_affineDiagonal :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [AlgebraicGeometry.IsAffine X]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))],
      AlgebraicGeometry.IsAffineHom g)

/- Lemma 29.11.12 (4): every morphism from an affine scheme to a separated scheme is
affine. -/
@[stacks 01SG] #check
  (AlgebraicGeometry.isAffineHom_of_isAffine_of_isSeparated :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [AlgebraicGeometry.IsAffine X]
      [AlgebraicGeometry.Scheme.IsSeparated Y], AlgebraicGeometry.IsAffineHom g)
