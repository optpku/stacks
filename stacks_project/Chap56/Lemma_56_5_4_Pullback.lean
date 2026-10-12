/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.BaseChange

@[expose] public section

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- The pullback comparison morphisms and their projection laws. -/
#check
  (AlgebraicGeometry.Scheme.QCoh.pullbackMapFst :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
      (x : X ⟶ Spec (CommRingCat.of R)) →
      (y : Y ⟶ Spec (CommRingCat.of R)) →
      ∀ {X' : Scheme.{u}}, (f : X' ⟶ X) →
        Limits.pullback (f ≫ x) y ⟶ Limits.pullback x y)

#check
  (AlgebraicGeometry.Scheme.QCoh.pullbackMapSnd :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
      (x : X ⟶ Spec (CommRingCat.of R)) →
      (y : Y ⟶ Spec (CommRingCat.of R)) →
      ∀ {Y' : Scheme.{u}}, (g : Y' ⟶ Y) →
        Limits.pullback x (g ≫ y) ⟶ Limits.pullback x y)

#check
  (AlgebraicGeometry.Scheme.QCoh.pullbackMapFst_fst :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
      (x : X ⟶ Spec (CommRingCat.of R)) →
      (y : Y ⟶ Spec (CommRingCat.of R)) →
      ∀ {X' : Scheme.{u}}, (f : X' ⟶ X) →
        AlgebraicGeometry.Scheme.QCoh.pullbackMapFst x y f ≫
            Limits.pullback.fst x y =
          Limits.pullback.fst (f ≫ x) y ≫ f)

#check
  (AlgebraicGeometry.Scheme.QCoh.pullbackMapSnd_snd :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
      (x : X ⟶ Spec (CommRingCat.of R)) →
      (y : Y ⟶ Spec (CommRingCat.of R)) →
      ∀ {Y' : Scheme.{u}}, (g : Y' ⟶ Y) →
        AlgebraicGeometry.Scheme.QCoh.pullbackMapSnd x y g ≫
            Limits.pullback.snd x y =
          Limits.pullback.snd x (g ≫ y) ≫ g)
