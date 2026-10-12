/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidScheme.ChangeAmbient

/-!
# Base change from the invariant spectrum of an affine groupoid scheme

This module constructs the invariant-spectrum presentation of an affine groupoid and its
base change along an explicit map from the invariant equalizer ring.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The map from the affine object scheme to the spectrum of its invariant equalizer. -/
def invariantSpectrumMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (target : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) :
    G.U.left ⟶ Spec (CommRingCat.of (target.eqLocus (algebraMap A B))) :=
  eU.inv ≫ Spec.map (CommRingCat.ofHom (target.eqLocus (algebraMap A B)).subtype)

/-- The original endpoint maps have the same composite to the invariant spectrum. -/
theorem invariantSpectrumMap_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (target : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left =
      Spec.map (CommRingCat.ofHom target) ≫ eU.hom) :
    G.t.left ≫ invariantSpectrumMap G target eU =
      G.s.left ≫ invariantSpectrumMap G target eU := sorry

/-- The original groupoid regarded over the spectrum of its invariant equalizer. -/
def overInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (target : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left =
      Spec.map (CommRingCat.ofHom target) ≫ eU.hom) :
    GroupoidScheme (Spec (CommRingCat.of (target.eqLocus (algebraMap A B)))) :=
  changeAmbient G (invariantSpectrumMap G target eU)
    (invariantSpectrumMap_eq G target eU eR h_source h_target)

/-- The object projection from invariant base change to the original object scheme. -/
def invariantBaseChangeObjectProjection {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (GroupoidScheme.baseChange (Spec.map (CommRingCat.ofHom γ))
      (overInvariantSpectrum G target eU eR h_source h_target)).U.left ⟶ G.U.left :=
  pullback.fst (invariantSpectrumMap G target eU) (Spec.map (CommRingCat.ofHom γ))

/-- The arrow projection from invariant base change to the original arrow scheme. -/
def invariantBaseChangeArrowProjection {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (GroupoidScheme.baseChange (Spec.map (CommRingCat.ofHom γ))
      (overInvariantSpectrum G target eU eR h_source h_target)).R.left ⟶ G.R.left :=
  pullback.fst
    ((overInvariantSpectrum G target eU eR h_source h_target).R.hom)
    (Spec.map (CommRingCat.ofHom γ))

/-- The two base-changed endpoint maps remain equal after composing with the original structure
map to `S`. -/
theorem invariantBaseChange_over_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    let H := GroupoidScheme.baseChange (Spec.map (CommRingCat.ofHom γ))
      (overInvariantSpectrum G target eU eR h_source h_target)
    H.t.left ≫ invariantBaseChangeObjectProjection G target eU eR h_source h_target γ ≫
        G.U.hom =
      H.s.left ≫ invariantBaseChangeObjectProjection G target eU eR h_source h_target γ ≫
        G.U.hom := sorry

/-- The groupoid obtained after extending the invariant coefficient ring. Its object and arrow
schemes are the corresponding affine tensor-product base changes. -/
def invariantBaseChange {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') : GroupoidScheme S :=
  let H := GroupoidScheme.baseChange (Spec.map (CommRingCat.ofHom γ))
    (overInvariantSpectrum G target eU eR h_source h_target)
  changeAmbient H
    (invariantBaseChangeObjectProjection G target eU eR h_source h_target γ ≫ G.U.hom)
    (invariantBaseChange_over_condition G target eU eR h_source h_target γ)


end AlgebraicGeometry.GroupoidScheme
