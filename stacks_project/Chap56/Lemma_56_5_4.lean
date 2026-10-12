/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.BaseChange

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 56.5.4 (1): affine pushforward on the first factor pulls back the
kernel along the corresponding fiber-product morphism. -/
@[stacks 0FZF] #check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukai_comp_pushforward :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X] [IsAffineHom f]
      (K : Scheme.QCoh (Limits.pullback x y)),
      IsIsomorphic (Scheme.QCoh.pushforward f ⋙
          AlgebraicGeometry.Scheme.QCoh.fourierMukai x y K)
        (AlgebraicGeometry.Scheme.QCoh.fourierMukai (f ≫ x) y
          ((Scheme.QCoh.pullback
            (AlgebraicGeometry.Scheme.QCoh.pullbackMapFst x y f)).obj K)))

/- Lemma 56.5.4 (2): flat pullback on the second factor pulls back the kernel
along the corresponding fiber-product morphism. -/
@[stacks 0FZF] #check
  (AlgebraicGeometry.Scheme.QCoh.pullback_comp_fourierMukai :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsAffine X] [Flat g]
      (K : Scheme.QCoh (Limits.pullback x y)),
      IsIsomorphic (AlgebraicGeometry.Scheme.QCoh.fourierMukai x y K ⋙
          Scheme.QCoh.pullback g)
        (AlgebraicGeometry.Scheme.QCoh.fourierMukai x (g ≫ y)
          ((Scheme.QCoh.pullback
            (AlgebraicGeometry.Scheme.QCoh.pullbackMapSnd x y g)).obj K)))

/- Lemma 56.5.4 (3): restriction along an open immersion on the second factor
pulls back the kernel along the corresponding fiber-product morphism. -/
@[stacks 0FZF] #check
  (AlgebraicGeometry.Scheme.QCoh.openImmersion_comp_fourierMukai :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      {V : Scheme.{u}} (j : V ⟶ Y) [IsAffine X] [IsOpenImmersion j]
      (K : Scheme.QCoh (Limits.pullback x y)),
      IsIsomorphic (AlgebraicGeometry.Scheme.QCoh.fourierMukai x y K ⋙
          Scheme.QCoh.pullback j)
        (AlgebraicGeometry.Scheme.QCoh.fourierMukai x (j ≫ y)
          ((Scheme.QCoh.pullback
            (AlgebraicGeometry.Scheme.QCoh.pullbackMapSnd x y j)).obj K)))
