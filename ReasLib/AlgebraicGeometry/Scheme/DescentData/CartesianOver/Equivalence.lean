/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.CartesianOver
public import ReasLib.AlgebraicTopology.SimplicialObject.Descent

/-!
# Cartesian schemes over a Čech nerve and descent data

The degree-zero descent construction and explicit simplicial reconstruction form
an equivalence for every morphism of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject CategoryTheory.Arrow

noncomputable section

-- Keep the private reconstruction reducible inside the public functors.
set_option backward.privateInPublic true

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Degree-zero components commute with the structure maps to the Čech base. -/
private theorem ofCartesianOverMap_over {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) :
    (φ.hom.left.app (op ⦋0⦌)) ≫ (schemeOver f Z.obj.hom).hom = (schemeOver f Y.obj.hom).hom := sorry

private def ofCartesianOverComponentMap
    {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) :
    schemeOver f Y.obj.hom ⟶ schemeOver f Z.obj.hom :=
  Over.homMk (φ.hom.left.app (op ⦋0⦌)) (ofCartesianOverMap_over f φ)

/-- Degree-zero components respect all descent comparisons. -/
private theorem ofCartesianOverMap_comm {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z)
    {T : Scheme.{u}} (q : T ⟶ S) {i j : PUnit.{v + 1}}
    (g₁ g₂ : T ⟶ X) (h₁ : g₁ ≫ f = q) (h₂ : g₂ ≫ f = q) :
    (Over.pullback g₁).map (ofCartesianOverComponentMap f φ) ≫
      (ofCartesianOver f Z).hom q (i₁ := i) (i₂ := j) g₁ g₂ h₁ h₂ =
    (ofCartesianOver f Y).hom q (i₁ := i) (i₂ := j) g₁ g₂ h₁ h₂ ≫
      (Over.pullback g₂).map (ofCartesianOverComponentMap f φ) := sorry

/-- The morphism of descent data induced by a morphism of cartesian schemes over the
Čech nerve of `f`, using the degree-zero component over `X`. -/
def ofCartesianOverMap {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) :
    ofCartesianOver f Y ⟶ ofCartesianOver f Z where
  hom _ := ofCartesianOverComponentMap f φ
  comm {T} q {i j} g₁ g₂ h₁ h₂ := ofCartesianOverMap_comm f φ (T := T) q (i := i) (j := j) g₁ g₂ h₁ h₂

/-- The degree-zero map preserves identity morphisms. -/
private theorem ofCartesianOverMap_id (Y : CartesianOver f.simplicialScheme) :
    ofCartesianOverMap f (𝟙 Y) = 𝟙 (ofCartesianOver f Y) := sorry

/-- The degree-zero map preserves composition. -/
private theorem ofCartesianOverMap_comp {Y Z W : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) (ψ : Z ⟶ W) :
    ofCartesianOverMap f (φ ≫ ψ) = ofCartesianOverMap f φ ≫ ofCartesianOverMap f ψ := sorry

/-- The functor sending a cartesian simplicial scheme over `f.simplicialScheme` to the
associated descent datum relative to `f`. -/
def ofCartesianOverFunctor :
    CartesianOver f.simplicialScheme ⥤
      DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) where
  obj Y := ofCartesianOver f Y
  map φ := ofCartesianOverMap f φ
  map_id := ofCartesianOverMap_id f
  map_comp := ofCartesianOverMap_comp f

/-- On objects, `ofCartesianOverFunctor f` is `ofCartesianOver f`. -/
theorem ofCartesianOverFunctor_obj (Y : CartesianOver f.simplicialScheme) :
    (ofCartesianOverFunctor.{u, v} f).obj Y = ofCartesianOver f Y := rfl

/-- The scheme over `(X/S)_0` obtained by transporting the unique component of a descent
datum along the degree-zero Čech identification `(X/S)_0 ≅ X`. -/
private def toCartesianDatumSchemeOver
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    Over (f.simplicialScheme.obj (op ⦋0⦌)) :=
  (Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj (D.obj default)

/-- The forward face transport commutes with the component structure map. -/
private theorem overPullbackFaceOneIso_hom_w_left (V : Over X) :
    ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom = (𝟙 V.left) ≫ V.hom := sorry

/-- The forward Čech identification commutes with the face projection. -/
private theorem overPullbackFaceOneIso_hom_w_right (V : Over X) :
    (f.simplicialScheme.δ (1 : Fin 2)) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom = (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom ≫ (pullback.fst f f) := sorry

/-- The inverse face transport commutes with the component structure map. -/
private theorem overPullbackFaceOneIso_inv_w_left (V : Over X) :
    V.hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv = (𝟙 V.left) ≫ ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom := sorry

/-- The inverse Čech identification commutes with the face projection. -/
private theorem overPullbackFaceOneIso_inv_w_right (V : Over X) :
    (pullback.fst f f) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv = (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv ≫ (f.simplicialScheme.δ (1 : Fin 2)) := sorry

private def overPullbackFaceOneIsoHom (V : Over X) :=
  pullback.map ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom
      (f.simplicialScheme.δ (1 : Fin 2)) V.hom (pullback.fst f f) (𝟙 _)
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom (cechNerve.degreeZero.iso (Arrow.mk f)).hom
      (overPullbackFaceOneIso_hom_w_left f V) (overPullbackFaceOneIso_hom_w_right f V)

private def overPullbackFaceOneIsoInv (V : Over X) :=
  pullback.map V.hom (pullback.fst f f)
      ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom (f.simplicialScheme.δ (1 : Fin 2)) (𝟙 _)
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv (cechNerve.degreeZero.iso (Arrow.mk f)).inv
      (overPullbackFaceOneIso_inv_w_left f V) (overPullbackFaceOneIso_inv_w_right f V)

/-- The forward face transport followed by its inverse is the identity. -/
private theorem overPullbackFaceOneIso_hom_inv_id (V : Over X) :
    overPullbackFaceOneIsoHom f V ≫ overPullbackFaceOneIsoInv f V = 𝟙 _ := sorry

/-- The inverse face transport followed by the forward transport is the identity. -/
private theorem overPullbackFaceOneIso_inv_hom_id (V : Over X) :
    overPullbackFaceOneIsoInv f V ≫ overPullbackFaceOneIsoHom f V = 𝟙 _ := sorry

/-- The face transport is a morphism over degree one of the Čech nerve. -/
private theorem overPullbackFaceOneIso_over (V : Over X) :
    overPullbackFaceOneIsoHom f V ≫
      (((Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj ((Over.pullback (pullback.fst f f)).obj V)).hom) =
      ((Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).obj ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V)).hom := sorry

/-- The degree-one Čech identification matches face `1` with the `fst` projection. -/
private def overPullbackFaceOneIso (V : Over X) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).obj ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V) ≅
      (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj ((Over.pullback (pullback.fst f f)).obj V) :=
  Over.isoMk
    { hom := overPullbackFaceOneIsoHom f V
      inv := overPullbackFaceOneIsoInv f V
      hom_inv_id := overPullbackFaceOneIso_hom_inv_id f V
      inv_hom_id := overPullbackFaceOneIso_inv_hom_id f V }
    (overPullbackFaceOneIso_over f V)

/-- The forward face transport commutes with the component structure map. -/
private theorem overPullbackFaceZeroIso_hom_w_left (V : Over X) :
    ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom = (𝟙 V.left) ≫ V.hom := sorry

/-- The forward Čech identification commutes with the face projection. -/
private theorem overPullbackFaceZeroIso_hom_w_right (V : Over X) :
    (f.simplicialScheme.δ (0 : Fin 2)) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom = (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom ≫ (pullback.snd f f) := sorry

/-- The inverse face transport commutes with the component structure map. -/
private theorem overPullbackFaceZeroIso_inv_w_left (V : Over X) :
    V.hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv = (𝟙 V.left) ≫ ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom := sorry

/-- The inverse Čech identification commutes with the face projection. -/
private theorem overPullbackFaceZeroIso_inv_w_right (V : Over X) :
    (pullback.snd f f) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv = (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv ≫ (f.simplicialScheme.δ (0 : Fin 2)) := sorry

private def overPullbackFaceZeroIsoHom (V : Over X) :=
  pullback.map ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom
      (f.simplicialScheme.δ (0 : Fin 2)) V.hom (pullback.snd f f) (𝟙 _)
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom (cechNerve.degreeZero.iso (Arrow.mk f)).hom
      (overPullbackFaceZeroIso_hom_w_left f V) (overPullbackFaceZeroIso_hom_w_right f V)

private def overPullbackFaceZeroIsoInv (V : Over X) :=
  pullback.map V.hom (pullback.snd f f)
      ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom (f.simplicialScheme.δ (0 : Fin 2)) (𝟙 _)
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv (cechNerve.degreeZero.iso (Arrow.mk f)).inv
      (overPullbackFaceZeroIso_inv_w_left f V) (overPullbackFaceZeroIso_inv_w_right f V)

/-- The forward face transport followed by its inverse is the identity. -/
private theorem overPullbackFaceZeroIso_hom_inv_id (V : Over X) :
    overPullbackFaceZeroIsoHom f V ≫ overPullbackFaceZeroIsoInv f V = 𝟙 _ := sorry

/-- The inverse face transport followed by the forward transport is the identity. -/
private theorem overPullbackFaceZeroIso_inv_hom_id (V : Over X) :
    overPullbackFaceZeroIsoInv f V ≫ overPullbackFaceZeroIsoHom f V = 𝟙 _ := sorry

/-- The face transport is a morphism over degree one of the Čech nerve. -/
private theorem overPullbackFaceZeroIso_over (V : Over X) :
    overPullbackFaceZeroIsoHom f V ≫
      (((Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj ((Over.pullback (pullback.snd f f)).obj V)).hom) =
      ((Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).obj ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V)).hom := sorry

/-- The degree-one Čech identification matches face `0` with the `snd` projection. -/
private def overPullbackFaceZeroIso (V : Over X) :
    (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).obj ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V) ≅
      (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj ((Over.pullback (pullback.snd f f)).obj V) :=
  Over.isoMk
    { hom := overPullbackFaceZeroIsoHom f V
      inv := overPullbackFaceZeroIsoInv f V
      hom_inv_id := overPullbackFaceZeroIso_hom_inv_id f V
      inv_hom_id := overPullbackFaceZeroIso_inv_hom_id f V }
    (overPullbackFaceZeroIso_over f V)

/-- The face-pullback isomorphism of a descent datum, transported to an isomorphism over
`(X/S)_1` between the `δ 1` and `δ 0` pullbacks. -/
private def toCartesianDatumIso
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).obj
        (toCartesianDatumSchemeOver f D) ≅
      (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).obj
        (toCartesianDatumSchemeOver f D) :=
  overPullbackFaceOneIso f (D.obj default) ≪≫
    (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).mapIso
      (CategoryTheory.Pseudofunctor.DescentData.iso D (pullback.fst f f ≫ f)
        (pullback.fst f f) (pullback.snd f f) rfl pullback.condition.symm) ≪≫
    (overPullbackFaceZeroIso f (D.obj default)).symm

/-- Transported descent comparisons restrict to the identity along the degeneracy. -/
private theorem toCartesianDatum_degeneracy (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    degeneracyPullback f.simplicialScheme (toCartesianDatumIso f D) =
      𝟙 (toCartesianDatumSchemeOver f D) := sorry

/-- Transported descent comparisons satisfy the simplicial cocycle equation. -/
private theorem toCartesianDatum_cocycle (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    cocycleLeft f.simplicialScheme (toCartesianDatumIso f D) =
      cocycleRight f.simplicialScheme (toCartesianDatumIso f D) := sorry

private def toCartesianDatumObj (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    CartesianDatum f.simplicialScheme :=
  CartesianDatum.ofPullbackIso (toCartesianDatumSchemeOver f D)
    (toCartesianDatumIso f D) (toCartesianDatum_degeneracy f D) (toCartesianDatum_cocycle f D)

/-- Transporting a descent morphism respects the face comparison. -/
private theorem toCartesianDatum_map_comm {D E : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)} (φ : D ⟶ E) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).map ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).map (φ.hom default)) ≫
      (toCartesianDatumObj f E).iso.hom =
    (toCartesianDatumObj f D).iso.hom ≫
      (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).map ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).map (φ.hom default)) := sorry

private def toCartesianDatumMap {D E : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)} (φ : D ⟶ E) :
    toCartesianDatumObj f D ⟶ toCartesianDatumObj f E :=
  CartesianDatum.homMk ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).map (φ.hom default)) (toCartesianDatum_map_comm f φ)

/-- Transport of descent morphisms preserves identities. -/
private theorem toCartesianDatum_map_id (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    toCartesianDatumMap f (𝟙 D) = 𝟙 (toCartesianDatumObj f D) := sorry

/-- Transport of descent morphisms preserves composition. -/
private theorem toCartesianDatum_map_comp {D E F : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)} (φ : D ⟶ E) (ψ : E ⟶ F) :
    toCartesianDatumMap f (φ ≫ ψ) = toCartesianDatumMap f φ ≫ toCartesianDatumMap f ψ := sorry

/-- Descent data transport to degree-zero objects with simplicial face comparisons. -/
private def toCartesianDatum :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) ⥤ CartesianDatum f.simplicialScheme where
  obj D := toCartesianDatumObj f D
  map φ := toCartesianDatumMap f φ
  map_id := toCartesianDatum_map_id f
  map_comp := toCartesianDatum_map_comp f

/-- The underlying scheme over `(X/S)_0` of `toCartesianDatum f` is the unique descent
component transported along the degree-zero Čech identification. -/
private theorem toCartesianDatum_schemeOver
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    ((toCartesianDatum f).obj D).schemeOver =
      Over.mk ((D.obj default).hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv) :=
  rfl

/-- The quasi-inverse of `ofCartesianOverFunctor f`, reconstructing a cartesian simplicial
scheme from a descent datum via `CartesianDatum.ofDatum`. -/
def ofCartesianOverInverse :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) ⥤
      CartesianOver f.simplicialScheme :=
  toCartesianDatum f ⋙ CartesianDatum.ofDatum

/-- The identity comparison of degree-zero components lies over the Čech base. -/
private theorem toCartesianDatumCompare_hom_over (Y : CartesianOver f.simplicialScheme) :
    (𝟙 (CartesianDatum.toDatum.obj Y).schemeOver.left) ≫ ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).schemeOver.hom =
      (CartesianDatum.toDatum.obj Y).schemeOver.hom := sorry

private def toCartesianDatumCompareHomOver (Y : CartesianOver f.simplicialScheme) :
    (CartesianDatum.toDatum.obj Y).schemeOver ⟶ ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).schemeOver :=
  Over.homMk (𝟙 _) (toCartesianDatumCompare_hom_over.{u, v} f Y)

/-- The identity comparison of degree-zero components respects face comparisons. -/
private theorem toCartesianDatumCompare_hom_comm (Y : CartesianOver f.simplicialScheme) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).map
        (toCartesianDatumCompareHomOver f Y) ≫ ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).iso.hom =
      (CartesianDatum.toDatum.obj Y).iso.hom ≫
        (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).map (toCartesianDatumCompareHomOver f Y) := sorry

private def toCartesianDatumCompareHom (Y : CartesianOver f.simplicialScheme) :
    (CartesianDatum.toDatum.obj Y) ⟶ ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)) :=
  CartesianDatum.homMk (toCartesianDatumCompareHomOver f Y) (toCartesianDatumCompare_hom_comm f Y)

/-- The identity comparison of degree-zero components lies over the Čech base. -/
private theorem toCartesianDatumCompare_inv_over (Y : CartesianOver f.simplicialScheme) :
    (𝟙 ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).schemeOver.left) ≫ (CartesianDatum.toDatum.obj Y).schemeOver.hom =
      ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).schemeOver.hom := sorry

private def toCartesianDatumCompareInvOver (Y : CartesianOver f.simplicialScheme) :
    ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).schemeOver ⟶ (CartesianDatum.toDatum.obj Y).schemeOver :=
  Over.homMk (𝟙 _) (toCartesianDatumCompare_inv_over.{u, v} f Y)

/-- The identity comparison of degree-zero components respects face comparisons. -/
private theorem toCartesianDatumCompare_inv_comm (Y : CartesianOver f.simplicialScheme) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).map
        (toCartesianDatumCompareInvOver f Y) ≫ (CartesianDatum.toDatum.obj Y).iso.hom =
      ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)).iso.hom ≫
        (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).map (toCartesianDatumCompareInvOver f Y) := sorry

private def toCartesianDatumCompareInv (Y : CartesianOver f.simplicialScheme) :
    ((toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y)) ⟶ (CartesianDatum.toDatum.obj Y) :=
  CartesianDatum.homMk (toCartesianDatumCompareInvOver f Y) (toCartesianDatumCompare_inv_comm f Y)

/-- The forward comparison followed by its inverse is the identity. -/
private theorem toCartesianDatumCompare_hom_inv_id (Y : CartesianOver f.simplicialScheme) :
    toCartesianDatumCompareHom f Y ≫ toCartesianDatumCompareInv f Y = 𝟙 _ := sorry

/-- The inverse comparison followed by the forward comparison is the identity. -/
private theorem toCartesianDatumCompare_inv_hom_id (Y : CartesianOver f.simplicialScheme) :
    toCartesianDatumCompareInv f Y ≫ toCartesianDatumCompareHom f Y = 𝟙 _ := sorry

/-- Direct extraction and extraction through scheme descent have isomorphic cartesian data. -/
private def toCartesianDatumCompare (Y : CartesianOver f.simplicialScheme) :
    CartesianDatum.toDatum.obj Y ≅ (toCartesianDatum f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y) where
  hom := toCartesianDatumCompareHom f Y
  inv := toCartesianDatumCompareInv f Y
  hom_inv_id := toCartesianDatumCompare_hom_inv_id f Y
  inv_hom_id := toCartesianDatumCompare_inv_hom_id f Y

/-- The unit isomorphism of the cartesian-over / descent-data equivalence, at an object
`Y`. -/
private def ofCartesianOverUnitApp (Y : CartesianOver f.simplicialScheme) :
    Y ≅ (ofCartesianOverInverse f).obj ((ofCartesianOverFunctor.{u, v} f).obj Y) :=
  CartesianDatum.unitApp Y ≪≫
    CartesianDatum.ofDatum.mapIso (toCartesianDatumCompare f Y)

/-- The explicit unit components are natural in cartesian simplicial schemes. -/
private theorem ofCartesianOverUnitIso_naturality {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) :
    (𝟭 (CartesianOver f.simplicialScheme)).map φ ≫ (ofCartesianOverUnitApp f Z).hom =
      (ofCartesianOverUnitApp f Y).hom ≫
        (ofCartesianOverFunctor f ⋙ ofCartesianOverInverse f).map φ := sorry

/-- The unit natural isomorphism `𝟭 ≅ ofCartesianOverFunctor f ⋙ ofCartesianOverInverse f`. -/
private def ofCartesianOverUnitIso :
    𝟭 (CartesianOver f.simplicialScheme) ≅
      ofCartesianOverFunctor f ⋙ ofCartesianOverInverse f :=
  NatIso.ofComponents (fun Y ↦ ofCartesianOverUnitApp f Y) (ofCartesianOverUnitIso_naturality f)

/-- Degree-zero comparison over `X` between the reconstructed descent component and the
original unique component of `D`, obtained by transporting `CartesianDatum.counitSchemeOverIso`
along the degree-zero Čech identification. -/
private def ofCartesianOverCounitOverIso
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    ((ofCartesianOverFunctor f).obj ((ofCartesianOverInverse f).obj D)).obj default ≅
      D.obj default :=
  (Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).hom).mapIso
      (CartesianDatum.counitSchemeOverIso ((toCartesianDatum f).obj D)) ≪≫
    (Over.mapIso (cechNerve.degreeZero.iso (Arrow.mk f))).counitIso.app (D.obj default)

/-- The degree-zero counit comparison respects every scheme descent comparison. -/
private theorem ofCartesianOverCounitApp_comm (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    {T : Scheme.{u}} (q : T ⟶ S) {i j : PUnit.{v + 1}}
    (g₁ g₂ : T ⟶ X) (h₁ : g₁ ≫ f = q) (h₂ : g₂ ≫ f = q) :
    (Over.pullback g₁).map (ofCartesianOverCounitOverIso.{u, v, u + 1} f D).hom ≫
      D.hom q (i₁ := i) (i₂ := j) g₁ g₂ h₁ h₂ =
    ((ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f).obj D).hom q (i₁ := i) (i₂ := j) g₁ g₂ h₁ h₂ ≫
      (Over.pullback g₂).map (ofCartesianOverCounitOverIso.{u, v, u + 1} f D).hom := sorry

/-- The counit isomorphism of the cartesian-over / descent-data equivalence, at a descent
datum `D`. -/
private def ofCartesianOverCounitApp
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    (ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f).obj D ≅ D :=
  CategoryTheory.Pseudofunctor.DescentData.isoMk
    (fun (_ : PUnit.{v + 1}) ↦ ofCartesianOverCounitOverIso.{u, v, u + 1} f D) (by
      intro T q i j g₁ g₂ h₁ h₂
      exact ofCartesianOverCounitApp_comm f D (T := T) q (i := i) (j := j) g₁ g₂ h₁ h₂)

/-- The explicit counit components are natural in scheme descent data. -/
private theorem ofCartesianOverCounitIso_naturality {D E : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)} (φ : D ⟶ E) :
    (ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f).map φ ≫
      (ofCartesianOverCounitApp f E).hom =
    (ofCartesianOverCounitApp f D).hom ≫ (𝟭 _).map φ := sorry

/-- The counit natural isomorphism
`ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f ≅ 𝟭`. -/
private def ofCartesianOverCounitIso :
    ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f ≅
      𝟭 (DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :=
  NatIso.ofComponents (fun D ↦ ofCartesianOverCounitApp f D) (ofCartesianOverCounitIso_naturality f)

/-- Cartesian simplicial schemes over the Čech nerve of a scheme morphism are
 equivalent to descent data relative to that morphism. -/
def ofCartesianOverEquivalence :
    CartesianOver f.simplicialScheme ≌
      DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) :=
  CategoryTheory.Equivalence.mk (ofCartesianOverFunctor f) (ofCartesianOverInverse f)
    (ofCartesianOverUnitIso f) (ofCartesianOverCounitIso f)

/-- The forward functor of `ofCartesianOverEquivalence f` is `ofCartesianOverFunctor f`. -/
theorem ofCartesianOverEquivalence_functor {X S : Scheme.{u}} (f : X ⟶ S) :
    (ofCartesianOverEquivalence f).functor = ofCartesianOverFunctor f := rfl

/-- The inverse functor of `ofCartesianOverEquivalence f` is `ofCartesianOverInverse f`. -/
theorem ofCartesianOverEquivalence_inverse {X S : Scheme.{u}} (f : X ⟶ S) :
    (ofCartesianOverEquivalence f).inverse = ofCartesianOverInverse f := rfl

/-- On objects, the forward functor of `ofCartesianOverEquivalence f` is the
degree-zero descent construction `ofCartesianOver f`. -/
theorem ofCartesianOverEquivalence_functor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : CartesianOver f.simplicialScheme) :
    (ofCartesianOverEquivalence f).functor.obj Y = ofCartesianOver f Y := rfl

end AlgebraicGeometry.Scheme.DescentData

