/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantBaseChange

/-!
# Invariant-ring maps of affine groupoid schemes

This module constructs the map on affine coordinate rings induced by a groupoid-scheme
morphism and restricts it to the equalizer subrings of invariant functions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace Hom

/-- The map on affine object-coordinate rings induced by a groupoid-scheme morphism. -/
def objectRingMap {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : Hom G' G)
    {A A' : Type u} [CommRing A] [CommRing A']
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left) : A →+* A' :=
  (Spec.preimage (eU'.hom ≫ F.obj.left ≫ eU.inv)).hom

/-- Applying `Spec` to `objectRingMap` recovers the object component in the chosen affine
presentations. -/
theorem objectRingMap_specMap {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A A' : Type u} [CommRing A] [CommRing A']
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left) :
    Spec.map (CommRingCat.ofHom (F.objectRingMap eU eU')) =
      eU'.hom ≫ F.obj.left ≫ eU.inv := sorry

/-- The map on affine arrow-coordinate rings induced by a groupoid-scheme morphism. -/
def arrowRingMap {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : Hom G' G)
    {B B' : Type u} [CommRing B] [CommRing B']
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left) : B →+* B' :=
  (Spec.preimage (eR'.hom ≫ F.arrow.left ≫ eR.inv)).hom

/-- Applying `Spec` to `arrowRingMap` recovers the arrow component in the chosen affine
presentations. -/
theorem arrowRingMap_specMap {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {B B' : Type u} [CommRing B] [CommRing B']
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left) :
    Spec.map (CommRingCat.ofHom (F.arrowRingMap eR eR')) =
      eR'.hom ≫ F.arrow.left ≫ eR.inv := sorry

/-- In affine presentations, the induced coordinate-ring maps commute with the source
homomorphisms. -/
theorem objectRingMap_source {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom) :
    (F.arrowRingMap eR eR').comp (algebraMap A B) =
      (algebraMap A' B').comp (F.objectRingMap eU eU') := sorry

/-- In affine presentations, the induced coordinate-ring maps commute with the target
homomorphisms. -/
theorem objectRingMap_target {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_target : eR.hom ≫ G.t.left =
      Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom) :
    (F.arrowRingMap eR eR').comp target =
      target'.comp (F.objectRingMap eU eU') := sorry

/-- The object-coordinate map sends invariant functions to invariant functions. -/
theorem invariantRingMap_condition {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom)
    (x : target.eqLocus (algebraMap A B)) :
    F.objectRingMap eU eU' x ∈ target'.eqLocus (algebraMap A' B') := sorry

/-- The homomorphism from invariant functions on the target groupoid to invariant functions
on the source groupoid. -/
def invariantRingMap {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : Hom G' G)
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom) :
    target.eqLocus (algebraMap A B) →+* target'.eqLocus (algebraMap A' B') :=
  RingHom.codRestrict
    ((F.objectRingMap eU eU').comp (target.eqLocus (algebraMap A B)).subtype)
    (target'.eqLocus (algebraMap A' B'))
    (fun x ↦ F.invariantRingMap_condition target target' eU eR eU' eR'
      h_source h_target h_source' h_target' x)

/-- The invariant-ring homomorphism is the restriction of the induced object-coordinate
homomorphism. -/
theorem invariantRingMap_apply {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom)
    (x : target.eqLocus (algebraMap A B)) :
    (F.invariantRingMap target target' eU eR eU' eR' h_source h_target h_source'
      h_target' x).val = F.objectRingMap eU eU' x := sorry

/-- The invariant-spectrum maps commute with the object component of a groupoid-scheme
morphism and its induced invariant-ring homomorphism. -/
theorem invariantSpectrumMap_naturality {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom) :
    F.obj.left ≫ invariantSpectrumMap G target eU =
      invariantSpectrumMap G' target' eU' ≫
        Spec.map (CommRingCat.ofHom (F.invariantRingMap target target' eU eR eU' eR'
          h_source h_target h_source' h_target')) := sorry

end Hom

end AlgebraicGeometry.GroupoidScheme
