/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Points of an algebraic space

A point of an algebraic space `X` over a scheme `S` is an equivalence class of morphisms
`Spec(K) ⟶ X` from spectra of fields, as objects of `Sch/S`. Two such morphisms are equivalent
when they become equal after restriction along a common field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by a morphism of schemes over `S`. -/
def ofOverMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) : ofOver U ⟶ ofOver V :=
  (yoneda.map f : yoneda.obj U ⟶ yoneda.obj V)

/-- `ofOverMap f` is the Yoneda image of a morphism of schemes over `S`. -/
theorem ofOverMap_eq {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    ofOverMap f = yoneda.map f := rfl

/-- The morphism of algebraic spaces over `S` induced by a morphism of schemes compatible with the
given structure morphisms. -/
def ofOverHomMk {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (f : XK ⟶ XL) (hf : f ≫ σL = σK) : ofOver (Over.mk σK) ⟶ ofOver (Over.mk σL) :=
  ofOverMap (Over.homMk f hf)

/-- `ofOverHomMk f hf` is `ofOverMap` of the corresponding morphism in `Over S`. -/
theorem ofOverHomMk_eq {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (f : XK ⟶ XL) (hf : f ≫ σL = σK) :
    ofOverHomMk f hf = ofOverMap (Over.homMk f hf) := rfl

set_option backward.privateInPublic true in
/-- Explicit field and morphism data for a field-valued point of an algebraic space. -/
private structure FieldValuedPointObj {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The source field. -/
  K : Type u
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The structure morphism of `Spec(K)` over `S`. -/
  structureHom : Spec (.of K) ⟶ S
  /-- The morphism `Spec(K) ⟶ X` of algebraic spaces over `S`. -/
  hom : ofOver (Over.mk structureHom) ⟶ X

set_option backward.privateInPublic true in
/-- The slice object over `X` determined by the stored field-valued morphism. -/
private def FieldValuedPointObj.over {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPointObj X) : Over X :=
  Over.mk p.hom

set_option backward.privateInPublic true in
/-- Field-valued points with morphisms induced from the slice category over the algebraic space. -/
abbrev FieldValuedPoint {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  InducedCategory (Over X) (FieldValuedPointObj.over (X := X))

namespace FieldValuedPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

set_option backward.privateInPublic true in
/-- The source-field carrier of a field-valued point. -/
abbrev K (p : FieldValuedPoint X) : Type u := FieldValuedPointObj.K p

set_option backward.privateInPublic true in
/-- The field structure stored in a field-valued point. -/
abbrev field (p : FieldValuedPoint X) : Field p.K := FieldValuedPointObj.field p

attribute [instance] field

set_option backward.privateInPublic true in
/-- The structure morphism from the source-field spectrum to the base scheme. -/
abbrev structureHom (p : FieldValuedPoint X) : Spec (.of p.K) ⟶ S :=
  FieldValuedPointObj.structureHom p

set_option backward.privateInPublic true in
/-- The morphism from the source-field spectrum into the algebraic space. -/
abbrev hom (p : FieldValuedPoint X) : ofOver (Over.mk p.structureHom) ⟶ X :=
  FieldValuedPointObj.hom p

set_option backward.privateInPublic true in
/-- The object over `X` determined by the field-valued point. -/
def over (p : FieldValuedPoint X) : Over X := FieldValuedPointObj.over p

/-- The induced embedding of field-valued points into the slice over `X`. -/
def toOver (X : AlgebraicSpace S) : FieldValuedPoint X ⥤ Over X :=
  inducedFunctor FieldValuedPoint.over

/-- The induced slice embedding of field-valued points is fully faithful. -/
def toOverFullyFaithful (X : AlgebraicSpace S) : (toOver X).FullyFaithful :=
  fullyFaithfulInducedFunctor FieldValuedPoint.over

set_option backward.privateInPublic true in
/-- Construct a field-valued point from a field, a structure morphism to `S`, and a morphism into
`X`. -/
def of (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) : FieldValuedPoint X :=
  ⟨K, structureHom, hom⟩

/-- The structure morphism of `FieldValuedPoint.of` is the given morphism to `S`. -/
@[simp]
theorem of_structureHom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).structureHom = structureHom := sorry

/-- The morphism into `X` of `FieldValuedPoint.of` is the given morphism. -/
@[simp]
theorem of_hom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).hom = hom := sorry

/-- The scheme over `S` given by the structure morphism of a field-valued point. -/
abbrev overObj (p : FieldValuedPoint X) : Over S :=
  Over.mk p.structureHom

/-- The structure morphism of `overObj p` is `p.structureHom`. -/
@[simp]
theorem overObj_hom (p : FieldValuedPoint X) : p.overObj.hom = p.structureHom := rfl

set_option backward.privateInPublic true in
/-- Postcompose a field-valued point with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) : FieldValuedPoint Y :=
  { K := p.K
    field := p.field
    structureHom := p.structureHom
    hom := p.hom ≫ f }

/-- Postcomposition leaves the structure morphism unchanged. -/
@[simp]
theorem map_structureHom {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).structureHom = p.structureHom := sorry

/-- The morphism of a postcomposed field-valued point is the evident composite. -/
@[simp]
theorem map_hom {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).hom = p.hom ≫ f := sorry

/-- The Yoneda element `p ∈ X(Spec(K))` determined by a field-valued point. -/
def elem (p : FieldValuedPoint X) : X.functorOfPoints.obj (op p.overObj) :=
  yonedaEquiv (p.hom : yoneda.obj p.overObj ⟶ X.functorOfPoints)

/-- The Yoneda element of a field-valued point recovers its morphism into `X`. -/
theorem elem_spec (p : FieldValuedPoint X) :
    yonedaEquiv.symm p.elem = p.hom := sorry

/-- A factorization from `p` to `q` is a morphism of source field spectra over `S` compatible with
the morphisms into `X`. Existence of such a factorization says that `p` dominates `q`. -/
structure Factorization (p q : FieldValuedPoint X) where
  /-- The morphism of source field spectra. -/
  schemeHom : p.overObj.left ⟶ q.overObj.left
  /-- The triangle over `S` commutes. -/
  fac_structure : schemeHom ≫ q.structureHom = p.structureHom
  /-- The triangle over `X` commutes. -/
  fac_hom : ofOverHomMk schemeHom fac_structure ≫ q.hom = p.hom

namespace Factorization

/-- Construct a factorization from a morphism of field spectra together with the two commuting
triangles. -/
def of {p q : FieldValuedPoint X} (schemeHom : p.overObj.left ⟶ q.overObj.left)
    (fac_structure : schemeHom ≫ q.structureHom = p.structureHom)
    (fac_hom : ofOverHomMk schemeHom fac_structure ≫ q.hom = p.hom) :
    Factorization p q where
  schemeHom := schemeHom
  fac_structure := fac_structure
  fac_hom := fac_hom

/-- The identity factorization commutes with the structure morphisms. -/
theorem refl_fac_structure (p : FieldValuedPoint X) :
    (𝟙 p.overObj.left) ≫ p.structureHom = p.structureHom := by simp

/-- The identity factorization commutes with the morphisms into `X`. -/
theorem refl_fac_hom (p : FieldValuedPoint X) :
    ofOverHomMk (𝟙 p.overObj.left) (refl_fac_structure p) ≫ p.hom = p.hom := by
  rw [ofOverHomMk_eq, ofOverMap_eq]
  have heq : Over.homMk (𝟙 p.overObj.left) (refl_fac_structure p) = 𝟙 p.overObj := by
    apply Over.OverMorphism.ext
    change (𝟙 p.overObj.left) = 𝟙 p.overObj.left
    rfl
  exact congrArg (fun k ↦ yoneda.map k ≫ p.hom) heq

/-- The identity factorization of a field-valued point. -/
def refl (p : FieldValuedPoint X) : Factorization p p where
  schemeHom := 𝟙 _
  fac_structure := refl_fac_structure p
  fac_hom := refl_fac_hom p

/-- Postcomposition preserves the structure-morphism triangle of a factorization. -/
theorem map_fac_structure {Y : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) (f : X ⟶ Y) :
    φ.schemeHom ≫ (q.map f).structureHom = (p.map f).structureHom := sorry

/-- Postcomposition preserves the morphism triangle of a factorization. -/
theorem map_fac_hom {Y : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) (f : X ⟶ Y) :
    ofOverHomMk φ.schemeHom (map_fac_structure φ f) ≫ (q.map f).hom = (p.map f).hom := sorry

/-- Postcompose a factorization with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (φ : Factorization p q) (f : X ⟶ Y) :
    Factorization (p.map f) (q.map f) where
  schemeHom := φ.schemeHom
  fac_structure := map_fac_structure φ f
  fac_hom := map_fac_hom φ f

/-- A factorization is a morphism of field spectra making both the `S`-triangle and the `X`-triangle
commute. -/
theorem spec {p q : FieldValuedPoint X} (φ : Factorization p q) :
    φ.schemeHom ≫ q.structureHom = p.structureHom ∧
      ofOverHomMk φ.schemeHom φ.fac_structure ≫ q.hom = p.hom := sorry

end Factorization

/-- A common extension of `p` and `q` is a field-valued point dominating both of them. -/
structure CommonExtension (p q : FieldValuedPoint X) where
  /-- The common field-valued extension. -/
  point : FieldValuedPoint X
  /-- Its factorization through `p`. -/
  left : Factorization point p
  /-- Its factorization through `q`. -/
  right : Factorization point q

namespace CommonExtension

/-- Build a common extension from a field-valued point and factorizations through `p` and `q`. -/
def of {p q : FieldValuedPoint X} (point : FieldValuedPoint X) (left : Factorization point p)
    (right : Factorization point q) : CommonExtension p q where
  point := point
  left := left
  right := right

/-- The tautological common extension of a field-valued point with itself. -/
def refl (p : FieldValuedPoint X) : CommonExtension p p where
  point := p
  left := Factorization.refl p
  right := Factorization.refl p

/-- Reverse the two legs of a common extension. -/
def symm {p q : FieldValuedPoint X} (e : CommonExtension p q) : CommonExtension q p where
  point := e.point
  left := e.right
  right := e.left

/-- Postcompose both legs of a common extension with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (e : CommonExtension p q) (f : X ⟶ Y) :
    CommonExtension (p.map f) (q.map f) where
  point := e.point.map f
  left := e.left.map f
  right := e.right.map f

end CommonExtension

/-- Field-valued points are equivalent when they admit a common field-valued extension over `X`. -/
def Equivalent (p q : FieldValuedPoint X) : Prop :=
  Nonempty (CommonExtension p q)

/-- Equivalence of field-valued points is reflexive. -/
theorem Equivalent.refl (p : FieldValuedPoint X) : Equivalent p p :=
  ⟨CommonExtension.refl p⟩

/-- Equivalence of field-valued points is symmetric. -/
theorem Equivalent.symm {p q : FieldValuedPoint X} : Equivalent p q → Equivalent q p := by
  rintro ⟨e⟩
  exact ⟨CommonExtension.symm e⟩

private theorem ofOverHomMk_comp {S : Scheme.{u}} {A B C : Scheme.{u}}
    {a : A ⟶ S} {b : B ⟶ S} {c : C ⟶ S}
    (f : A ⟶ B) (g : B ⟶ C) (hf : f ≫ b = a) (hg : g ≫ c = b) :
    ofOverHomMk f hf ≫ ofOverHomMk g hg =
      ofOverHomMk (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  rw [ofOverHomMk_eq, ofOverHomMk_eq, ofOverHomMk_eq]
  apply yoneda.map_injective
  ext U x
  rfl

private theorem field_amalgam {K L M : Type u} [Field K] [Field L] [Field M]
    (f : Spec (.of K) ⟶ Spec (.of M)) (g : Spec (.of L) ⟶ Spec (.of M)) :
    ∃ (Ω : Type u) (_ : Field Ω) (i : Spec (.of Ω) ⟶ Spec (.of K))
      (j : Spec (.of Ω) ⟶ Spec (.of L)), i ≫ f = j ≫ g := by
  let φ : CommRingCat.of M ⟶ CommRingCat.of K := Spec.homEquiv f
  let ψ : CommRingCat.of M ⟶ CommRingCat.of L := Spec.homEquiv g
  letI : Algebra M K := φ.hom.toAlgebra
  letI : Algebra M L := ψ.hom.toAlgebra
  let A := K ⊗[M] L
  haveI : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain M K L
      (RingHom.injective _) (RingHom.injective _)
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  let R : CommRingCat := (Spec (.of A)).residueField x
  let Ω : Type u := R.carrier
  let z : Spec (.of Ω) ⟶ Spec (.of A) := (Spec (.of A)).fromSpecResidueField x
  let e := pullbackSpecIso M K L
  let i : Spec (.of Ω) ⟶ Spec (.of K) :=
    z ≫ e.inv ≫ Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap M K)))
      (Spec.map (CommRingCat.ofHom (algebraMap M L)))
  let j : Spec (.of Ω) ⟶ Spec (.of L) :=
    z ≫ e.inv ≫ Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap M K)))
      (Spec.map (CommRingCat.ofHom (algebraMap M L)))
  have hf : Spec.map (CommRingCat.ofHom (algebraMap M K)) = f := by
    change Spec.map φ = f
    exact Spec.map_preimage f
  have hg : Spec.map (CommRingCat.ofHom (algebraMap M L)) = g := by
    change Spec.map ψ = g
    exact Spec.map_preimage g
  have hij : i ≫ f = j ≫ g := by
    have hpb :
        Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap M K)))
            (Spec.map (CommRingCat.ofHom (algebraMap M L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap M K)) =
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap M K)))
            (Spec.map (CommRingCat.ofHom (algebraMap M L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap M L)) :=
      Limits.pullback.condition
    simpa [i, j, Category.assoc, hf, hg] using
      congrArg (fun k ↦ z ≫ e.inv ≫ k) hpb
  exact ⟨Ω, inferInstance, i, j, hij⟩

/-- Equivalence of field-valued points is transitive. -/
theorem Equivalent.trans {p q r : FieldValuedPoint X} :
    Equivalent p q → Equivalent q r → Equivalent p r := by
  rintro ⟨e₁⟩ ⟨e₂⟩
  let f := e₁.right.schemeHom
  let g := e₂.left.schemeHom
  let hfam := field_amalgam f g
  let Ω : Type u := Classical.choose hfam
  letI : Field Ω := Classical.choose (Classical.choose_spec hfam)
  let hiData := Classical.choose_spec (Classical.choose_spec hfam)
  let i : Spec (.of Ω) ⟶ e₁.point.overObj.left := Classical.choose hiData
  let hjData := Classical.choose_spec hiData
  let j : Spec (.of Ω) ⟶ e₂.point.overObj.left := Classical.choose hjData
  have hij : i ≫ f = j ≫ g := Classical.choose_spec hjData
  let σ : Spec (.of Ω) ⟶ S := i ≫ e₁.point.structureHom
  let hiOver : i ≫ e₁.point.overObj.hom = σ := by
    rfl
  let hi : i ≫ e₁.point.structureHom = σ := by
    simpa only [overObj_hom] using hiOver
  let hjOver : j ≫ e₂.point.overObj.hom = σ := by
    change j ≫ e₂.point.overObj.hom = i ≫ e₁.point.overObj.hom
    have hl : e₁.right.schemeHom ≫ q.overObj.hom = e₁.point.overObj.hom := by
      simpa only [overObj_hom] using e₁.right.fac_structure
    have hr : e₂.left.schemeHom ≫ q.overObj.hom = e₂.point.overObj.hom := by
      simpa only [overObj_hom] using e₂.left.fac_structure
    rw [← hr, ← hl]
    rw [← Category.assoc, ← Category.assoc, hij]
  let hj : j ≫ e₂.point.structureHom = σ := by
    simpa only [overObj_hom] using hjOver
  let cHom : ofOver (Over.mk σ) ⟶ X :=
    ofOverHomMk i hi ≫ e₁.point.hom
  let c : FieldValuedPoint X := FieldValuedPoint.of Ω σ cHom
  have hleftOver : e₁.right.schemeHom ≫ q.overObj.hom = e₁.point.overObj.hom := by
    simpa only [overObj_hom] using e₁.right.fac_structure
  have hrightOver : e₂.left.schemeHom ≫ q.overObj.hom = e₂.point.overObj.hom := by
    simpa only [overObj_hom] using e₂.left.fac_structure
  have hif :
      (i ≫ e₁.right.schemeHom) ≫ q.overObj.hom = σ := by
    rw [Category.assoc, hleftOver]
    exact hiOver
  have hjg :
      (j ≫ e₂.left.schemeHom) ≫ q.overObj.hom = σ := by
    rw [Category.assoc, hrightOver]
    exact hjOver
  have hmap :
      ofOverHomMk (i ≫ e₁.right.schemeHom) hif =
        ofOverHomMk (j ≫ e₂.left.schemeHom) hjg := by
    rw [ofOverHomMk_eq, ofOverHomMk_eq]
    exact congrArg yoneda.map (Over.OverMorphism.ext hij)
  have hcomp₁ :
      ofOverHomMk i hi ≫ ofOverHomMk e₁.right.schemeHom e₁.right.fac_structure =
        ofOverHomMk (i ≫ e₁.right.schemeHom) hif := by
    convert ofOverHomMk_comp i e₁.right.schemeHom hi e₁.right.fac_structure using 1 <;> simp
  have hcomp₂ :
      ofOverHomMk j hj ≫ ofOverHomMk e₂.left.schemeHom e₂.left.fac_structure =
        ofOverHomMk (j ≫ e₂.left.schemeHom) hjg := by
    convert ofOverHomMk_comp j e₂.left.schemeHom hj e₂.left.fac_structure using 1 <;> simp
  have hpath :
      ofOverHomMk i hi ≫ e₁.point.hom =
        ofOverHomMk j hj ≫ e₂.point.hom := by
    calc
      ofOverHomMk i hi ≫ e₁.point.hom =
          ofOverHomMk i hi ≫ (ofOverHomMk e₁.right.schemeHom e₁.right.fac_structure ≫ q.hom) := by
            exact congrArg (fun k ↦ ofOverHomMk i hi ≫ k) e₁.right.fac_hom.symm
      _ = (ofOverHomMk i hi ≫ ofOverHomMk e₁.right.schemeHom e₁.right.fac_structure) ≫ q.hom := by
            simp only [Category.assoc]
      _ = ofOverHomMk (i ≫ e₁.right.schemeHom) hif ≫ q.hom := by exact congrArg (fun k ↦ k ≫ q.hom) hcomp₁
      _ = ofOverHomMk (j ≫ e₂.left.schemeHom) hjg ≫ q.hom := by rw [hmap]
      _ = (ofOverHomMk j hj ≫ ofOverHomMk e₂.left.schemeHom e₂.left.fac_structure) ≫ q.hom := by
            exact congrArg (fun k ↦ k ≫ q.hom) hcomp₂.symm
      _ = ofOverHomMk j hj ≫ (ofOverHomMk e₂.left.schemeHom e₂.left.fac_structure ≫ q.hom) := by
            simp only [Category.assoc]
      _ = ofOverHomMk j hj ≫ e₂.point.hom := by
            exact congrArg (fun k ↦ ofOverHomMk j hj ≫ k) e₂.left.fac_hom
  have hleftStruct :
      (i ≫ e₁.left.schemeHom) ≫ p.structureHom = σ := by
    rw [Category.assoc, e₁.left.fac_structure]
  let left : Factorization c p := {
    schemeHom := i ≫ e₁.left.schemeHom
    fac_structure := hleftStruct
    fac_hom := by
      change ofOverHomMk (i ≫ e₁.left.schemeHom) hleftStruct ≫ p.hom =
        ofOverHomMk i hi ≫ e₁.point.hom
      have hcomp :
          ofOverHomMk i hi ≫ ofOverHomMk e₁.left.schemeHom e₁.left.fac_structure =
            ofOverHomMk (i ≫ e₁.left.schemeHom) hleftStruct := by
        convert ofOverHomMk_comp i e₁.left.schemeHom hi e₁.left.fac_structure using 1
      calc
        ofOverHomMk (i ≫ e₁.left.schemeHom) hleftStruct ≫ p.hom =
            (ofOverHomMk i hi ≫ ofOverHomMk e₁.left.schemeHom e₁.left.fac_structure) ≫ p.hom := by
              exact congrArg (fun k ↦ k ≫ p.hom) hcomp.symm
        _ = ofOverHomMk i hi ≫ (ofOverHomMk e₁.left.schemeHom e₁.left.fac_structure ≫ p.hom) := by
              simp only [Category.assoc]
        _ = ofOverHomMk i hi ≫ e₁.point.hom := by
              exact congrArg (fun k ↦ ofOverHomMk i hi ≫ k) e₁.left.fac_hom
  }
  have hrightStruct :
      (j ≫ e₂.right.schemeHom) ≫ r.structureHom = σ := by
    rw [Category.assoc, e₂.right.fac_structure]
    exact hj
  let right : Factorization c r := {
    schemeHom := j ≫ e₂.right.schemeHom
    fac_structure := hrightStruct
    fac_hom := by
      change ofOverHomMk (j ≫ e₂.right.schemeHom) hrightStruct ≫ r.hom =
        ofOverHomMk i hi ≫ e₁.point.hom
      have hcomp :
          ofOverHomMk j hj ≫ ofOverHomMk e₂.right.schemeHom e₂.right.fac_structure =
            ofOverHomMk (j ≫ e₂.right.schemeHom) hrightStruct := by
        convert ofOverHomMk_comp j e₂.right.schemeHom hj e₂.right.fac_structure using 1
      calc
        ofOverHomMk (j ≫ e₂.right.schemeHom) hrightStruct ≫ r.hom =
            (ofOverHomMk j hj ≫ ofOverHomMk e₂.right.schemeHom e₂.right.fac_structure) ≫ r.hom := by
              exact congrArg (fun k ↦ k ≫ r.hom) hcomp.symm
        _ = ofOverHomMk j hj ≫ (ofOverHomMk e₂.right.schemeHom e₂.right.fac_structure ≫ r.hom) := by
              simp only [Category.assoc]
        _ = ofOverHomMk j hj ≫ e₂.point.hom := by
              exact congrArg (fun k ↦ ofOverHomMk j hj ≫ k) e₂.right.fac_hom
        _ = ofOverHomMk i hi ≫ e₁.point.hom := hpath.symm
  }
  exact ⟨CommonExtension.of c left right⟩
/-- Equivalence is preserved by postcomposition with a morphism of algebraic spaces over `S`. -/
theorem Equivalent.map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (h : Equivalent p q)
    (f : X ⟶ Y) : Equivalent (p.map f) (q.map f) := sorry

/-- Equivalence of field-valued points is the existence of a common field spectrum over `S` whose
restrictions recover the two morphisms into `X`. -/
theorem equivalent_iff (p q : FieldValuedPoint X) :
    Equivalent p q ↔
      ∃ (r : FieldValuedPoint X) (i : r.overObj.left ⟶ p.overObj.left)
        (j : r.overObj.left ⟶ q.overObj.left)
        (hi : i ≫ p.structureHom = r.structureHom)
        (hj : j ≫ q.structureHom = r.structureHom),
        ofOverHomMk i hi ≫ p.hom = ofOverHomMk j hj ≫ q.hom := sorry

end FieldValuedPoint

/-- The setoid of field-valued points of an algebraic space, with relation the common-extension
equivalence. -/
def equivalentSetoid {S : Scheme.{u}} (X : AlgebraicSpace S) : Setoid (FieldValuedPoint X) where
  r := FieldValuedPoint.Equivalent
  iseqv := {
    refl := FieldValuedPoint.Equivalent.refl
    symm := FieldValuedPoint.Equivalent.symm
    trans := FieldValuedPoint.Equivalent.trans
  }

/-- The setoid relation is the common-extension equivalence of field-valued points. -/
@[simp]
theorem equivalentSetoid_rel_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The set of points of an algebraic space, as equivalence classes of morphisms from spectra of
fields. -/
def Points {S : Scheme.{u}} (X : AlgebraicSpace S) : Type (u + 1) :=
  Quotient (equivalentSetoid X)

/-- The set of points of an algebraic space `X`. -/
scoped notation:max "|" X:max "|" => Points X

namespace Points

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The class of a field-valued point. -/
def mk (p : FieldValuedPoint X) : Points X :=
  Quotient.mk (equivalentSetoid X) p

/-- Two field-valued points determine the same point of `X` exactly when they admit a common
field-valued extension. -/
@[simp]
theorem mk_eq_mk_iff (p q : FieldValuedPoint X) :
    mk p = mk q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The map on points induced by a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} (f : X ⟶ Y) : Points X → Points Y :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦ FieldValuedPoint.Equivalent.map h f

/-- The induced map on points sends the class of a representative to the class of its
postcomposition. -/
@[simp]
theorem map_mk {Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint X) :
    map f (mk p) = mk (p.map f) := sorry

/-- The identity morphism of algebraic spaces induces the identity on points. -/
@[simp]
theorem map_id (x : Points X) : map (𝟙 X) x = x := sorry

/-- The induced map on points preserves composition. -/
@[simp]
theorem map_comp {Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) :
    map (f ≫ g) x = map g (map f x) := sorry

end Points

end AlgebraicGeometry.AlgebraicSpace
