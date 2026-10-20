/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.20.3: Affineness of a morphism of algebraic spaces is equivalent to
representable affineness, affineness of affine-scheme étale pullbacks,
affineness after a surjective étale scheme atlas, and affineness over a
Zariski covering of the target. -/
@[stacks 03WG] #check (AlgebraicGeometry.AlgebraicSpace.Affine.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.Affine.representableAffine f,
      AlgebraicGeometry.AlgebraicSpace.Affine f,
      AlgebraicGeometry.AlgebraicSpace.Affine.forallAffineEtale f,
      AlgebraicGeometry.AlgebraicSpace.Affine.existsSurjectiveEtaleTarget f,
      AlgebraicGeometry.AlgebraicSpace.Affine.existsZariskiCover f])
