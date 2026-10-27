/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

/-!
# Characterizations of closed immersions of formal algebraic spaces

Lemma 87.27.4 records that a morphism of formal algebraic spaces is a closed
immersion iff this is tested by closed-immersion projections after
scheme-valued and affine base change, by a Definition 87.11.1 étale atlas of
the target, and by a representable fppf morphism of formal algebraic spaces.
The final condition uses the corrected pullback projection `X ×_Y Z ⟶ Z`.
-/

/- Lemma 87.27.4: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: `ClosedImmersion f`; every
scheme-valued base change of `f` is a closed immersion (`forallScheme f`);
every affine-scheme-valued base change of `f` is a closed immersion
(`forallAffine f`); some covering `{Y_j ⟶ Y}` as in Definition 87.11.1 has
each base change `X ×_Y Y_j ⟶ Y_j` a closed immersion
(`existsCoverOnTarget f`); and some morphism `Z ⟶ Y` of formal algebraic
spaces that is representable by algebraic spaces, surjective, flat, and
locally of finite presentation has `X ×_Y Z ⟶ Z` a closed immersion
(`existsFppf f`). -/
@[stacks 0GHY] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.tfae :
    ∀ {S : Scheme} {X Y : (Over S)ᵒᵖ ⥤ Type}
      [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
      (f : X ⟶ Y),
      List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion f,
        AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.forallScheme f,
        AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.forallAffine f,
        AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.existsCoverOnTarget f,
        AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.existsFppf f])
