/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.AffineOpen

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Remark 56.5.8: for a quasi-compact scheme with affine diagonal, quasicoherent kernels
correspond to relatively linear, coproduct-preserving functors that are right exact after
affine-open pushforward and preserve initial exactness of stalkwise split short exact sequences. -/
@[stacks 0GPB] #check
  (AlgebraicGeometry.Scheme.QCoh.affineOpenFourierMukai_isEquivalence :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      (Scheme.QCoh.affineOpenFourierMukai x y).IsEquivalence)

#check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukai_affineOpenCoproductLinear :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      (K : Scheme.QCoh (Limits.pullback x y)),
      Scheme.QCoh.AffineOpenCoproductLinear x y (Scheme.QCoh.fourierMukai x y K))

#check
  (AlgebraicGeometry.Scheme.QCoh.exists_fourierMukai_iso_of_affineOpenCoproductLinear :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Scheme.QCoh.AffineOpenCoproductLinear x y F],
      ∃ (K : Scheme.QCoh (Limits.pullback x y)) (t : F ⟶ Scheme.QCoh.fourierMukai x y K),
        IsIso t)
