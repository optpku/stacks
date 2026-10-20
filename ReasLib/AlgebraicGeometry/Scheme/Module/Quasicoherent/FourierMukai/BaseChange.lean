/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Affine

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R]
variable {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))

/-- The morphism `f × id_Y` between the corresponding fiber products. -/
noncomputable def pullbackMapFst {X' : Scheme.{u}} (f : X' ⟶ X) :
    Limits.pullback (f ≫ x) y ⟶ Limits.pullback x y :=
  Limits.pullback.map (f ≫ x) y x y f (𝟙 Y) (𝟙 _)
    (Category.comp_id (f ≫ x))
    ((Category.comp_id y).trans (Category.id_comp y).symm)

/-- The morphism `id_X × g` between the corresponding fiber products. -/
noncomputable def pullbackMapSnd {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    Limits.pullback x (g ≫ y) ⟶ Limits.pullback x y :=
  Limits.pullback.map x (g ≫ y) x y (𝟙 X) g (𝟙 _)
    ((Category.comp_id x).trans (Category.id_comp x).symm)
    (Category.comp_id (g ≫ y))

/-- The first projection of `pullbackMapFst` is the pullback of `f`. -/
theorem pullbackMapFst_fst {X' : Scheme.{u}} (f : X' ⟶ X) :
    pullbackMapFst x y f ≫ Limits.pullback.fst x y =
      Limits.pullback.fst (f ≫ x) y ≫ f :=
  sorry

/-- The second projection of `pullbackMapSnd` is the pullback of `g`. -/
theorem pullbackMapSnd_snd {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    pullbackMapSnd x y g ≫ Limits.pullback.snd x y =
      Limits.pullback.snd x (g ≫ y) ≫ g :=
  sorry

/-- Affine pushforward on the first factor transports a Fourier--Mukai kernel by
pullback along the corresponding fiber-product morphism. -/
theorem fourierMukai_comp_pushforward {X' : Scheme.{u}} (f : X' ⟶ X)
    [IsAffine X] [IsAffineHom f] (K : Scheme.QCoh (Limits.pullback x y)) :
    IsIsomorphic (Scheme.QCoh.pushforward f ⋙ fourierMukai x y K)
      (fourierMukai (f ≫ x) y
        ((Scheme.QCoh.pullback (pullbackMapFst x y f)).obj K)) :=
  sorry

/-- Flat pullback on the second factor transports a Fourier--Mukai kernel by
pullback along the corresponding fiber-product morphism. -/
theorem pullback_comp_fourierMukai {Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsAffine X] [Flat g] (K : Scheme.QCoh (Limits.pullback x y)) :
    IsIsomorphic (fourierMukai x y K ⋙ Scheme.QCoh.pullback g)
      (fourierMukai x (g ≫ y)
        ((Scheme.QCoh.pullback (pullbackMapSnd x y g)).obj K)) :=
  sorry

/-- Restriction along an open immersion on the second factor transports a
Fourier--Mukai kernel by pullback along the corresponding fiber-product morphism. -/
theorem openImmersion_comp_fourierMukai {V : Scheme.{u}} (j : V ⟶ Y)
    [IsAffine X] [IsOpenImmersion j] (K : Scheme.QCoh (Limits.pullback x y)) :
    IsIsomorphic (fourierMukai x y K ⋙ Scheme.QCoh.pullback j)
      (fourierMukai x (j ≫ y)
        ((Scheme.QCoh.pullback (pullbackMapSnd x y j)).obj K)) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
