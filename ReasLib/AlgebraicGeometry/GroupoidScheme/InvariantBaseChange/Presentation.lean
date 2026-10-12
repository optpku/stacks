/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantBaseChange
public import ReasLib.RingTheory.RingHom.EqLocusBaseChange

/-!
# Affine presentations of invariant base change

This module identifies the object and arrow schemes of invariant base change with spectra of
tensor products and constructs the canonical projection to the original groupoid.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace InvariantBaseChange

/-- The first pullback square is carried to the standard affine-spectrum pullback square. -/
theorem objectPullbackMap_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    invariantSpectrumMap G target eU ≫ 𝟙 _ =
      eU.inv ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (target.eqLocus (algebraMap A B)) A)) := sorry

/-- The coefficient-side map is unchanged in the comparison of object pullbacks. -/
theorem objectPullbackMap_right {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    Spec.map (CommRingCat.ofHom γ) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom γ) := sorry


/-- The canonical isomorphism between the geometric object pullback and its standard affine
presentation. -/
def objectPullbackIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    let C := target.eqLocus (algebraMap A B)
    pullback (invariantSpectrumMap G target eU) (Spec.map (CommRingCat.ofHom γ)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap C A)))
        (Spec.map (CommRingCat.ofHom γ)) :=
  let C := target.eqLocus (algebraMap A B)
  let f := Spec.map (CommRingCat.ofHom γ)
  asIso (pullback.map (invariantSpectrumMap G target eU) f
    (Spec.map (CommRingCat.ofHom (algebraMap C A))) f eU.inv (𝟙 _) (𝟙 _)
    (objectPullbackMap_left G target eU eR h_source h_target γ)
    (objectPullbackMap_right G target eU eR h_source h_target γ))

/-- The object scheme of invariant base change is canonically the spectrum of
`A ⊗[target.eqLocus (algebraMap A B)] C'`. -/
noncomputable def objectIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (invariantBaseChange G target eU eR h_source h_target γ).U.left ≅
      -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
      Spec (CommRingCat.of (A ⊗[target.eqLocus (algebraMap A B)] C')) :=
  let C := target.eqLocus (algebraMap A B)
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra C C' := γ.toAlgebra
  objectPullbackIso G target eU eR h_source h_target γ ≪≫ pullbackSpecIso C A C'

/-- The object comparison isomorphism is the canonical comparison with the affine pullback. -/
theorem objectIso_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (objectIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) =
      invariantBaseChangeObjectProjection G target eU eR h_source h_target γ ≫ eU.inv := sorry

/-- The arrow pullback comparison commutes on the affine-arrow side. -/
theorem arrowPullbackMap_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (overInvariantSpectrum G target eU eR h_source h_target).R.hom ≫ 𝟙 _ =
      eR.inv ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap A B).comp (target.eqLocus (algebraMap A B)).subtype)) := sorry

/-- The coefficient-side map is unchanged in the comparison of arrow pullbacks. -/
theorem arrowPullbackMap_right {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    Spec.map (CommRingCat.ofHom γ) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom γ) := sorry


/-- The canonical isomorphism between the geometric arrow pullback and its standard affine
presentation. -/
def arrowPullbackIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    let C := target.eqLocus (algebraMap A B)
    pullback (overInvariantSpectrum G target eU eR h_source h_target).R.hom
        (Spec.map (CommRingCat.ofHom γ)) ≅
      pullback (Spec.map (CommRingCat.ofHom ((algebraMap A B).comp C.subtype)))
        (Spec.map (CommRingCat.ofHom γ)) :=
  let C := target.eqLocus (algebraMap A B)
  let f := Spec.map (CommRingCat.ofHom γ)
  let bMap := (algebraMap A B).comp C.subtype
  asIso (pullback.map (overInvariantSpectrum G target eU eR h_source h_target).R.hom f
    (Spec.map (CommRingCat.ofHom bMap)) f eR.inv (𝟙 _) (𝟙 _)
    (arrowPullbackMap_left G target eU eR h_source h_target γ)
    (arrowPullbackMap_right G target eU eR h_source h_target γ))

/-- The arrow scheme of invariant base change is canonically the spectrum of
`B ⊗[target.eqLocus (algebraMap A B)] C'`. -/
noncomputable def arrowIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (invariantBaseChange G target eU eR h_source h_target γ).R.left ≅
      -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
      letI : Algebra (target.eqLocus (algebraMap A B)) B :=
        ((algebraMap A B).comp (target.eqLocus (algebraMap A B)).subtype).toAlgebra
      -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
      Spec (CommRingCat.of (B ⊗[target.eqLocus (algebraMap A B)] C')) :=
  let C := target.eqLocus (algebraMap A B)
  -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
  letI : Algebra C B := ((algebraMap A B).comp C.subtype).toAlgebra
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra C C' := γ.toAlgebra
  arrowPullbackIso G target eU eR h_source h_target γ ≪≫ pullbackSpecIso C B C'

/-- The arrow comparison isomorphism is the canonical comparison with the affine pullback. -/
theorem arrowIso_spec {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (arrowIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) =
      invariantBaseChangeArrowProjection G target eU eR h_source h_target γ ≫ eR.inv := sorry

/-- The object projection is a morphism over `S`. -/
theorem projection_obj_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    invariantBaseChangeObjectProjection G target eU eR h_source h_target γ ≫ G.U.hom =
      (invariantBaseChange G target eU eR h_source h_target γ).U.hom := sorry

/-- The arrow projection is a morphism over `S`. -/
theorem projection_arrow_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    invariantBaseChangeArrowProjection G target eU eR h_source h_target γ ≫ G.R.hom =
      (invariantBaseChange G target eU eR h_source h_target γ).R.hom := sorry

/-- The groupoid projection commutes with source. -/
theorem projection_map_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (invariantBaseChange G target eU eR h_source h_target γ).s ≫
        Over.homMk (invariantBaseChangeObjectProjection G target eU eR h_source h_target γ)
          (projection_obj_condition G target eU eR h_source h_target γ) =
      Over.homMk (invariantBaseChangeArrowProjection G target eU eR h_source h_target γ)
          (projection_arrow_condition G target eU eR h_source h_target γ) ≫ G.s := sorry

/-- The groupoid projection commutes with target. -/
theorem projection_map_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (invariantBaseChange G target eU eR h_source h_target γ).t ≫
        Over.homMk (invariantBaseChangeObjectProjection G target eU eR h_source h_target γ)
          (projection_obj_condition G target eU eR h_source h_target γ) =
      Over.homMk (invariantBaseChangeArrowProjection G target eU eR h_source h_target γ)
          (projection_arrow_condition G target eU eR h_source h_target γ) ≫ G.t := sorry

/-- The groupoid projection commutes with composition. -/
theorem projection_map_composition {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    let H := invariantBaseChange G target eU eR h_source h_target γ
    let obj : H.U ⟶ G.U := Over.homMk
      (invariantBaseChangeObjectProjection G target eU eR h_source h_target γ)
      (projection_obj_condition G target eU eR h_source h_target γ)
    let arrow : H.R ⟶ G.R := Over.homMk
      (invariantBaseChangeArrowProjection G target eU eR h_source h_target γ)
      (projection_arrow_condition G target eU eR h_source h_target γ)
    H.c ≫ arrow = GroupoidScheme.composableMap obj arrow
      (projection_map_source G target eU eR h_source h_target γ)
      (projection_map_target G target eU eR h_source h_target γ) ≫ G.c := sorry

/-- The canonical projection from the invariant base-changed groupoid to the original groupoid. -/
def projection {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    GroupoidScheme.Hom (invariantBaseChange G target eU eR h_source h_target γ) G where
  obj := Over.homMk (invariantBaseChangeObjectProjection G target eU eR h_source h_target γ)
    (projection_obj_condition G target eU eR h_source h_target γ)
  arrow := Over.homMk (invariantBaseChangeArrowProjection G target eU eR h_source h_target γ)
    (projection_arrow_condition G target eU eR h_source h_target γ)
  map_s := projection_map_source G target eU eR h_source h_target γ
  map_t := projection_map_target G target eU eR h_source h_target γ
  map_c := projection_map_composition G target eU eR h_source h_target γ

/-- The object component of the invariant base-change projection is the first pullback
projection. -/
theorem projection_obj {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (projection G target eU eR h_source h_target γ).obj.left =
      invariantBaseChangeObjectProjection G target eU eR h_source h_target γ := sorry

/-- The arrow component of the invariant base-change projection is the first pullback
projection. -/
theorem projection_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    (projection G target eU eR h_source h_target γ).arrow.left =
      invariantBaseChangeArrowProjection G target eU eR h_source h_target γ := sorry

/-- Under the affine comparison isomorphisms, the source map is induced by the tensor-product
source homomorphism. -/
theorem source_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (arrowIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.EqLocusBaseChange.sourceComap target (algebraMap A B) γ)) =
      (invariantBaseChange G target eU eR h_source h_target γ).s.left ≫
        (objectIso G target eU eR h_source h_target γ).hom := sorry

/-- Under the affine comparison isomorphisms, the target map is induced by the tensor-product
target homomorphism. -/
theorem target_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
    (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (γ : target.eqLocus (algebraMap A B) →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (arrowIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.EqLocusBaseChange.targetComap target (algebraMap A B) γ)) =
      (invariantBaseChange G target eU eR h_source h_target γ).t.left ≫
        (objectIso G target eU eR h_source h_target γ).hom := sorry

end InvariantBaseChange

end AlgebraicGeometry.GroupoidScheme
