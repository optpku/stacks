/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineOnAffineSchemes
import StacksCheckRecall

/-!
# Affine representable morphisms of algebraic spaces

A representable morphism of algebraic spaces is affine in the sense of Section
67.3 if and only if every base change along a morphism from an affine scheme is
an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 67.20.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is affine in the sense of
Section 67.3 if and only if for all affine schemes `Z` and morphisms `Z ⟶ Y`
the scheme `X ×_Y Z` is affine. -/
@[stacks 03WE] #check
  (AlgebraicGeometry.AlgebraicSpace.isAffineHom_presheaf_iff_isAffineOnAffineSchemes :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
        ((over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f ↔
          AlgebraicGeometry.AlgebraicSpace.isAffineOnAffineSchemes f))
