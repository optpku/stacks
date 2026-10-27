/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-!
# Naive cotangent complexes of morphisms of algebraic spaces

The naive cotangent complex `NL_f` of a morphism of algebraic spaces is the two-term complex of
`𝒪_X`-modules on `X_étale` obtained by sheafifying the objectwise naive cotangent complex of the
inverse-image structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Algebra Algebra.Extension Algebra.Generators
open MvPolynomial
open scoped ZeroObject TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- The algebra structure on `𝒪_X(U)` over `f⁻¹𝒪_Y(U)`. -/
@[reducible] def inverseImageAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U) :=
  ((commInverseImageStructureSheafMap f).hom.app U).hom.toAlgebra

/-- The canonical self-presentation of `𝒪_X(U)` over `f⁻¹𝒪_Y(U)`. -/
def presentation {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : (smallEtaleSite X)ᵒᵖ) :=
  @Generators.self
    ((commInverseImageStructureSheaf f).obj.obj U)
    ((commStructureSheaf X).obj.obj U)
    _ _ (inverseImageAlgebra f U)

/-- The objectwise degree `-1` term `I / I ^ 2` of the canonical presentation. -/
def cotangentObj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u} ((commStructureSheaf X).obj.obj U) :=
  -- Local instance justification (noncanonical choice): algebra `f⁻¹𝒪_Y(U) → 𝒪_X(U)`.
  letI := inverseImageAlgebra f U
  ModuleCat.of _ (presentation f U).toExtension.Cotangent

/-- The objectwise degree `0` term of the canonical presentation. -/
def cotangentSpaceObj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u} ((commStructureSheaf X).obj.obj U) :=
  -- Local instance justification (noncanonical choice): algebra `f⁻¹𝒪_Y(U) → 𝒪_X(U)`.
  letI := inverseImageAlgebra f U
  ModuleCat.of _ (presentation f U).toExtension.CotangentSpace

/-- The polynomial ring map of canonical presentations induced by restriction along `i`. -/
def presentationRingHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    MvPolynomial ((commStructureSheaf X).obj.obj U)
        ((commInverseImageStructureSheaf f).obj.obj U) →+*
      MvPolynomial ((commStructureSheaf X).obj.obj V)
        ((commInverseImageStructureSheaf f).obj.obj V) :=
  (map ((commInverseImageStructureSheaf f).obj.map i).hom).comp
    (rename (fun s ↦ ((commStructureSheaf X).obj.map i).hom s)).toRingHom

/-- Restriction of `f⁻¹𝒪_Y` along `i`. -/
@[reducible] def inverseImageRestrictionAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V) :=
  ((commInverseImageStructureSheaf f).obj.map i).hom.toAlgebra

/-- Restriction of `𝒪_X` along `i`. -/
@[reducible] def structureRestrictionAlgebra {X : AlgebraicSpace S}
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    Algebra ((commStructureSheaf X).obj.obj U) ((commStructureSheaf X).obj.obj V) :=
  ((commStructureSheaf X).obj.map i).hom.toAlgebra

private theorem presentationRingHom_eval {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (eval₂Hom ((commInverseImageStructureSheafMap f).hom.app V).hom id).comp
        (presentationRingHom f i) =
      ((commStructureSheaf X).obj.map i).hom.comp
        (eval₂Hom ((commInverseImageStructureSheafMap f).hom.app U).hom id) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa [presentationRingHom] using
      DFunLike.congr_fun
        (congrArg CommRingCat.Hom.hom
          ((commInverseImageStructureSheafMap f).hom.naturality i)) r
  · intro r
    simp [presentationRingHom]

private theorem presentationRingHom_id {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    presentationRingHom f (𝟙 U) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro r <;> simp [presentationRingHom]

private theorem presentationRingHom_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V W : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    presentationRingHom f (i ≫ j) =
      (presentationRingHom f j).comp (presentationRingHom f i) := by
  apply MvPolynomial.ringHom_ext <;> intro r <;> simp [presentationRingHom]

/-- Polynomial restriction carries constant coefficients to their restricted values. -/
theorem presentationRingHom_commutes {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (r : ((commInverseImageStructureSheaf f).obj.obj U)) :
    -- Local instance justification (noncanonical choice): restriction along i fixes the target coefficient algebra over the source ring for the polynomial algebraMap in this statement.
    letI := inverseImageRestrictionAlgebra f i
    presentationRingHom f i (algebraMap ((commInverseImageStructureSheaf f).obj.obj U) (MvPolynomial ((commStructureSheaf X).obj.obj U) ((commInverseImageStructureSheaf f).obj.obj U)) r) =
      algebraMap ((commInverseImageStructureSheaf f).obj.obj U) (MvPolynomial ((commStructureSheaf X).obj.obj V) ((commInverseImageStructureSheaf f).obj.obj V)) r := by
  change presentationRingHom f i (C r) =
    C (((commInverseImageStructureSheaf f).obj.map i).hom r)
  simp [presentationRingHom]

/-- The algebra homomorphism of canonical presentations induced by restriction along `i`. -/
def presentationAlgHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :=
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i is the coefficient algebra of presentationAlgHom, not a global Algebra.
  letI := inverseImageRestrictionAlgebra f i
  ({ presentationRingHom f i with
      commutes' := presentationRingHom_commutes f i } :
    MvPolynomial ((commStructureSheaf X).obj.obj U)
        ((commInverseImageStructureSheaf f).obj.obj U) →ₐ[
          (commInverseImageStructureSheaf f).obj.obj U]
      MvPolynomial ((commStructureSheaf X).obj.obj V)
        ((commInverseImageStructureSheaf f).obj.obj V))

/-- Polynomial restriction maps the presentation kernel into the target presentation kernel. -/
theorem presentationAlgHom_ker_le_comap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Cotangent.of.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for the target kernel.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for presentationAlgHom.
  letI := inverseImageRestrictionAlgebra f i
  (presentation f U).ker ≤ (presentation f V).ker.comap (presentationAlgHom f i) := by
  intro p hp
  change eval₂Hom ((commInverseImageStructureSheafMap f).hom.app V).hom id
    (presentationRingHom f i p) = 0
  change eval₂Hom ((commInverseImageStructureSheafMap f).hom.app U).hom id p = 0 at hp
  calc
    _ = ((commStructureSheaf X).obj.map i).hom
        (eval₂Hom ((commInverseImageStructureSheafMap f).hom.app U).hom id p) :=
      RingHom.congr_fun (presentationRingHom_eval f i) p
    _ = 0 := by rw [hp, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction on conormal modules preserves addition. -/
theorem cotangentObj_mapFun_add {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (x y : cotangentObj f U) :
  -- Local instance justification (noncanonical choice): the source and target coefficient algebras and their restriction are fixed by the structure map.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): the target conormal construction uses the algebra supplied by the component of f^♯ at V; the ring types alone do not determine this map.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): the polynomial map used by Ideal.mapCotangent requires the coefficient algebra supplied by restriction along this particular i.
  letI := inverseImageRestrictionAlgebra f i
  let mapFun : cotangentObj f U → cotangentObj f V :=
    fun x ↦ Cotangent.of
        (Ideal.mapCotangent (presentation f U).ker (presentation f V).ker
          (presentationAlgHom f i) (presentationAlgHom_ker_le_comap f i)
          (Cotangent.val (P := (presentation f U).toExtension) x))
  mapFun (x + y) = mapFun x + mapFun y := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  letI := inverseImageRestrictionAlgebra f i
  exact congrArg (Cotangent.of (P := (presentation f V).toExtension))
    ((Ideal.mapCotangent (presentation f U).ker (presentation f V).ker
      (presentationAlgHom f i) (presentationAlgHom_ker_le_comap f i)).map_add
      (Cotangent.val x) (Cotangent.val y))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction on conormal modules is semilinear for restriction of scalars. -/
theorem cotangentObj_mapFun_smul {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (r : ((commStructureSheaf X).obj.obj U)) (x : cotangentObj f U) :
  -- Local instance justification (noncanonical choice): the source and target coefficient algebras and their restriction are fixed by the structure map.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): the target conormal construction uses the algebra supplied by the component of f^♯ at V; the ring types alone do not determine this map.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): the polynomial map used by Ideal.mapCotangent requires the coefficient algebra supplied by restriction along this particular i.
  letI := inverseImageRestrictionAlgebra f i
  let mapFun : cotangentObj f U → cotangentObj f V :=
    fun x ↦ Cotangent.of
        (Ideal.mapCotangent (presentation f U).ker (presentation f V).ker
          (presentationAlgHom f i) (presentationAlgHom_ker_le_comap f i)
          (Cotangent.val (P := (presentation f U).toExtension) x))
  mapFun (r • x) = ((commStructureSheaf X).obj.map i).hom r • mapFun x := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  letI := inverseImageRestrictionAlgebra f i
  letI := structureRestrictionAlgebra i
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let h : (presentation f U).toExtension.Hom (presentation f V).toExtension :=
    { toRingHom := presentationRingHom f i
      toRingHom_algebraMap := presentationRingHom_commutes f i
      algebraMap_toRingHom := fun p ↦ RingHom.congr_fun (presentationRingHom_eval f i) p }
  exact (Cotangent.map h).map_smul r x

/-- Restriction of the objectwise conormal module of the canonical presentation. -/
def cotangentObj_map {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    cotangentObj f U ⟶
      (ModuleCat.restrictScalars
        (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
        (cotangentObj f V) :=
  -- Local instance justification (noncanonical choice): the source and target coefficient algebras and their restriction are fixed by the structure map.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): the target conormal construction uses the algebra supplied by the component of f^♯ at V; the ring types alone do not determine this map.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): the polynomial map used by Ideal.mapCotangent requires the coefficient algebra supplied by restriction along this particular i.
  letI := inverseImageRestrictionAlgebra f i
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj U))
    { toFun := fun x ↦ Cotangent.of
        (Ideal.mapCotangent (presentation f U).ker (presentation f V).ker
          (presentationAlgHom f i) (presentationAlgHom_ker_le_comap f i)
          (Cotangent.val (P := (presentation f U).toExtension) x))
      map_add' := cotangentObj_mapFun_add f i
      map_smul' := cotangentObj_mapFun_smul f i }

/-- The composite coefficient algebra map factors through inverse-image restriction. -/
theorem inverseImageRestriction_algebraMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (r : ((commInverseImageStructureSheaf f).obj.obj U)) :
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Extension.Hom.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for Extension.Hom.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for Extension.Hom.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for Extension.Hom.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  algebraMap ((commInverseImageStructureSheaf f).obj.obj U) ((commStructureSheaf X).obj.obj V) r =
    algebraMap ((commInverseImageStructureSheaf f).obj.obj V) ((commStructureSheaf X).obj.obj V) (algebraMap ((commInverseImageStructureSheaf f).obj.obj U) ((commInverseImageStructureSheaf f).obj.obj V) r) := by
  rfl

/-- The composite coefficient algebra map factors through structure-sheaf restriction. -/
theorem structureRestriction_algebraMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (r : ((commInverseImageStructureSheaf f).obj.obj U)) :
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Extension.Hom.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for Extension.Hom.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for Extension.Hom.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for Extension.Hom.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  algebraMap ((commInverseImageStructureSheaf f).obj.obj U) ((commStructureSheaf X).obj.obj V) r =
    algebraMap ((commStructureSheaf X).obj.obj U) ((commStructureSheaf X).obj.obj V) (algebraMap ((commInverseImageStructureSheaf f).obj.obj U) ((commStructureSheaf X).obj.obj U) r) := by
  exact DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom
      ((commInverseImageStructureSheafMap f).hom.naturality i)) r

/-- Polynomial restriction commutes with the coefficient maps of the presentations. -/
theorem presentationRestrictHom_toRingHom_algebraMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (r : ((commInverseImageStructureSheaf f).obj.obj U)) :
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Extension.Hom.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for Extension.Hom.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for Extension.Hom.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for Extension.Hom.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  presentationRingHom f i
      (algebraMap ((commInverseImageStructureSheaf f).obj.obj U) (presentation f U).toExtension.Ring r) =
    algebraMap ((commInverseImageStructureSheaf f).obj.obj V) (presentation f V).toExtension.Ring
      (algebraMap ((commInverseImageStructureSheaf f).obj.obj U) ((commInverseImageStructureSheaf f).obj.obj V) r) := by
  exact presentationRingHom_commutes f i r

/-- Polynomial restriction commutes with evaluation in the structure sheaf. -/
theorem presentationRestrictHom_algebraMap_toRingHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (p : MvPolynomial ((commStructureSheaf X).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj U)) :
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Extension.Hom.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for Extension.Hom.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for Extension.Hom.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for Extension.Hom.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  algebraMap (presentation f V).toExtension.Ring ((commStructureSheaf X).obj.obj V) (presentationRingHom f i p) =
    algebraMap ((commStructureSheaf X).obj.obj U) ((commStructureSheaf X).obj.obj V)
      (algebraMap (presentation f U).toExtension.Ring ((commStructureSheaf X).obj.obj U) p) := by
  exact RingHom.congr_fun (presentationRingHom_eval f i) p

/-- The morphism of canonical presentations induced by restriction along `i`. -/
def presentationRestrictHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Extension.Hom.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for Extension.Hom.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for Extension.Hom.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for Extension.Hom.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  -- Local instance justification (noncanonical choice): scalar tower of inverse-image restriction into 𝒪_X(V), needed by Extension.Hom.
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (inverseImageRestriction_algebraMap_eq f i)
  -- Local instance justification (noncanonical choice): scalar tower of 𝒪_X restriction from U to V, needed by Extension.Hom.
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (structureRestriction_algebraMap_eq f i)
  ({ toRingHom := presentationRingHom f i
     toRingHom_algebraMap := presentationRestrictHom_toRingHom_algebraMap f i
     algebraMap_toRingHom := presentationRestrictHom_algebraMap_toRingHom f i } :
    ((presentation f U).toExtension).Hom ((presentation f V).toExtension))

/-- Restriction of the objectwise cotangent-space term of the canonical presentation. -/
def cotangentSpaceObj_map {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    cotangentSpaceObj f U ⟶
      (ModuleCat.restrictScalars
        (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
        (cotangentSpaceObj f V) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for CotangentSpace.map.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for CotangentSpace.map.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for CotangentSpace.map.
  letI := inverseImageRestrictionAlgebra f i
  -- Local instance justification (noncanonical choice): restriction of 𝒪_X along i for CotangentSpace.map.
  letI := structureRestrictionAlgebra i
  -- Local instance justification (noncanonical choice): composite algebra f⁻¹𝒪_Y(U) → 𝒪_X(V) is not globally canonical.
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  -- Local instance justification (noncanonical choice): scalar tower of inverse-image restriction into 𝒪_X(V), needed by CotangentSpace.map.
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (inverseImageRestriction_algebraMap_eq f i)
  -- Local instance justification (noncanonical choice): scalar tower of 𝒪_X restriction from U to V, needed by CotangentSpace.map.
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (structureRestriction_algebraMap_eq f i)
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj U))
    (CotangentSpace.map (presentationRestrictHom f i))

private theorem cotangentObj_map_mk {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    letI := inverseImageAlgebra f U
    letI := inverseImageAlgebra f V
    letI := inverseImageRestrictionAlgebra f i
    ∀ x : (presentation f U).ker,
      cotangentObj_map f i (Cotangent.mk x) =
        Cotangent.mk ⟨presentationRingHom f i x, presentationAlgHom_ker_le_comap f i x.2⟩ := by
  dsimp only
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem cotangentSpaceObj_map_tmul {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    letI := inverseImageAlgebra f U
    letI := inverseImageAlgebra f V
    ∀ (r : ((commStructureSheaf X).obj.obj U))
      (p : MvPolynomial ((commStructureSheaf X).obj.obj U)
        ((commInverseImageStructureSheaf f).obj.obj U)),
      cotangentSpaceObj_map f i
          (r ⊗ₜ KaehlerDifferential.D
            ((commInverseImageStructureSheaf f).obj.obj U) (presentation f U).toExtension.Ring p) =
        ((commStructureSheaf X).obj.map i).hom r ⊗ₜ
          KaehlerDifferential.D ((commInverseImageStructureSheaf f).obj.obj V)
            (presentation f V).toExtension.Ring (presentationRingHom f i p) := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  letI := inverseImageRestrictionAlgebra f i
  letI := structureRestrictionAlgebra i
  letI : Algebra ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app V).hom.comp
        ((commInverseImageStructureSheaf f).obj.map i).hom)
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (inverseImageRestriction_algebraMap_eq f i)
  letI : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U)
      ((commStructureSheaf X).obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (structureRestriction_algebraMap_eq f i)
  dsimp only
  intro r p
  exact CotangentSpace.map_tmul (presentationRestrictHom f i) r p

/-- Restriction of the conormal module along an identity is the scalar restriction identity. -/
theorem cotangentObj_map_id {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentObj_map f (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map_id U))).inv.app
        (cotangentObj f U) := by
  letI := inverseImageAlgebra f U
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective (P := (presentation f U).toExtension) x
  change cotangentObj_map f (𝟙 U) (Cotangent.mk x) = Cotangent.mk x
  rw [cotangentObj_map_mk]
  congr 1
  exact Subtype.ext (RingHom.congr_fun (presentationRingHom_id f U) x.val)

/-- Restriction of the conormal module respects composition with the scalar restriction comparison. -/
theorem cotangentObj_map_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V W : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    cotangentObj_map f (i ≫ j) =
      cotangentObj_map f i ≫ (ModuleCat.restrictScalars _).map (cotangentObj_map f j) ≫
        (ModuleCat.restrictScalarsComp'
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map j).hom)
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map_comp i j))).inv.app
          (cotangentObj f W) := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  letI := inverseImageAlgebra f W
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective (P := (presentation f U).toExtension) x
  change cotangentObj_map f (i ≫ j) (Cotangent.mk x) =
    cotangentObj_map f j (cotangentObj_map f i (Cotangent.mk x))
  rw [cotangentObj_map_mk, cotangentObj_map_mk, cotangentObj_map_mk]
  congr 1
  exact Subtype.ext (RingHom.congr_fun (presentationRingHom_comp f i j) x.val)

/-- The presheaf of conormal modules of the canonical presentations of `f^♯`. -/
def cotangentPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) where
  obj := cotangentObj f
  map := cotangentObj_map f
  map_id := cotangentObj_map_id f
  map_comp := cotangentObj_map_comp f

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the cotangent-space module along an identity is the scalar restriction identity. -/
theorem cotangentSpaceObj_map_id {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentSpaceObj_map f (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map_id U))).inv.app
        (cotangentSpaceObj f U) := by
  letI := inverseImageAlgebra f U
  apply ModuleCat.hom_ext
  apply (presentation f U).cotangentSpaceBasis.ext
  intro r
  rw [Generators.cotangentSpaceBasis_apply]
  change cotangentSpaceObj_map f (𝟙 U)
      (1 ⊗ₜ KaehlerDifferential.D ((commInverseImageStructureSheaf f).obj.obj U)
        (presentation f U).toExtension.Ring (MvPolynomial.X r)) =
    1 ⊗ₜ KaehlerDifferential.D ((commInverseImageStructureSheaf f).obj.obj U)
        (presentation f U).toExtension.Ring (MvPolynomial.X r)
  rw [cotangentSpaceObj_map_tmul]
  simp [presentationRingHom_id]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the cotangent-space module respects composition with the scalar restriction comparison. -/
theorem cotangentSpaceObj_map_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V W : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    cotangentSpaceObj_map f (i ≫ j) =
      cotangentSpaceObj_map f i ≫ (ModuleCat.restrictScalars _).map (cotangentSpaceObj_map f j) ≫
        (ModuleCat.restrictScalarsComp'
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map j).hom)
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map_comp i j))).inv.app
          (cotangentSpaceObj f W) := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  letI := inverseImageAlgebra f W
  apply ModuleCat.hom_ext
  apply (presentation f U).cotangentSpaceBasis.ext
  intro r
  rw [Generators.cotangentSpaceBasis_apply]
  change cotangentSpaceObj_map f (i ≫ j)
      (1 ⊗ₜ KaehlerDifferential.D ((commInverseImageStructureSheaf f).obj.obj U)
        (presentation f U).toExtension.Ring (MvPolynomial.X r)) =
    cotangentSpaceObj_map f j
      (cotangentSpaceObj_map f i (1 ⊗ₜ KaehlerDifferential.D ((commInverseImageStructureSheaf f).obj.obj U)
        (presentation f U).toExtension.Ring (MvPolynomial.X r)))
  rw [cotangentSpaceObj_map_tmul, cotangentSpaceObj_map_tmul, cotangentSpaceObj_map_tmul]
  simp [presentationRingHom_comp]

/-- The presheaf of base-changed presentation differentials of `f^♯`. -/
def cotangentSpacePresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) where
  obj := cotangentSpaceObj f
  map := cotangentSpaceObj_map f
  map_id := cotangentSpaceObj_map_id f
  map_comp := cotangentSpaceObj_map_comp f

/-- The objectwise conormal differential of the canonical presentation of `f^♯`. -/
def cotangentComplex_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentObj f U ⟶ cotangentSpaceObj f U :=
  -- Local instance justification (noncanonical choice): algebra `f⁻¹𝒪_Y(U) → 𝒪_X(U)`.
  letI := inverseImageAlgebra f U
  ModuleCat.ofHom (Extension.cotangentComplex (presentation f U).toExtension)

set_option backward.isDefEq.respectTransparency false in
/-- The objectwise conormal differential commutes with restriction. -/
theorem cotangentComplex_app_naturality {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (cotangentPresheaf f).map i ≫
        (ModuleCat.restrictScalars
          ((((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom)).map
          (cotangentComplex_app f V) =
      cotangentComplex_app f U ≫ (cotangentSpacePresheaf f).map i := by
  letI := inverseImageAlgebra f U
  letI := inverseImageAlgebra f V
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective (P := (presentation f U).toExtension) x
  change (presentation f V).toExtension.cotangentComplex
      (cotangentObj_map f i (Cotangent.mk x)) =
    cotangentSpaceObj_map f i
      ((presentation f U).toExtension.cotangentComplex (Cotangent.mk x))
  simp only [cotangentObj_map_mk, Extension.cotangentComplex_mk,
    cotangentSpaceObj_map_tmul, map_one]

/-- The presheaf morphism `I / I ^ 2 ⟶ 𝒪_X ⊗ Ω(P / f⁻¹𝒪_Y)` of canonical presentations. -/
def cotangentDifferentialPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    cotangentPresheaf f ⟶ cotangentSpacePresheaf f where
  app := cotangentComplex_app f
  naturality := cotangentComplex_app_naturality f

/-- The sheaf of modules `I / I ^ 2` of the canonical presentation of `f^♯`. -/
def cotangentSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
    (cotangentPresheaf f)

/-- The sheaf of modules `𝒪_X ⊗ Ω(P / f⁻¹𝒪_Y)` of the canonical presentation of `f^♯`. -/
def cotangentSpaceSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
    (cotangentSpacePresheaf f)

/-- The sheafified zero `𝒪_X`-module. -/
def zeroModuleSheaf (X : AlgebraicSpace S) : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
    (0 : PresheafOfModules.{u} (structureSheaf X).obj)

/-- Terms of the naive cotangent complex of a morphism of algebraic spaces. -/
def naiveCotangentTerm {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℤ) : X.Modules :=
  match n with
  | Int.negSucc 0 => cotangentSheaf f
  | Int.ofNat 0 => cotangentSpaceSheaf f
  | _ => zeroModuleSheaf X

/-- The sheafified conormal differential of a morphism of algebraic spaces. -/
def cotangentDifferential {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    cotangentSheaf f ⟶ cotangentSpaceSheaf f :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).map
    (cotangentDifferentialPresheaf f)

/-- Differentials of the naive cotangent complex of a morphism of algebraic spaces. -/
def naiveCotangentDifferential {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℤ) :
    naiveCotangentTerm f n ⟶ naiveCotangentTerm f (n + 1) :=
  match n with
  | Int.negSucc 0 => cotangentDifferential f
  | _ => 0

/-- Consecutive differentials of the naive cotangent complex square to zero. -/
theorem naiveCotangentDifferential_sq_zero {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (n : ℤ) :
    naiveCotangentDifferential f n ≫ naiveCotangentDifferential f (n + 1) = 0 := by
  cases n with
  | ofNat n => simp [naiveCotangentDifferential]
  | negSucc n =>
    cases n with
    | zero =>
      change cotangentDifferential f ≫ 0 = 0
      exact CategoryTheory.Limits.comp_zero
    | succ n => simp [naiveCotangentDifferential]

/-- The naive cotangent complex `NL_f` of a morphism of algebraic spaces, as an
`𝒪_X`-module complex on `X_étale`. -/
def naiveCotangent {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CochainComplex X.Modules ℤ :=
  CochainComplex.of (naiveCotangentTerm f) (naiveCotangentDifferential f)
    (naiveCotangentDifferential_sq_zero f)

/-- `NL_f` is the two-term complex of sheafified canonical-presentation cotangent terms. -/
theorem naiveCotangent_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    naiveCotangent f =
      CochainComplex.of (naiveCotangentTerm f) (naiveCotangentDifferential f)
        (naiveCotangentDifferential_sq_zero f) :=
  rfl

/-- The degree `-1` term of `NL_f` is the sheafification of `I / I ^ 2`. -/
theorem naiveCotangent_X_negOne {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (naiveCotangent f).X (-1) = cotangentSheaf f := by
  rfl

/-- The degree `0` term of `NL_f` is the sheafification of `𝒪_X ⊗ Ω(P / f⁻¹𝒪_Y)`. -/
theorem naiveCotangent_X_zero {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (naiveCotangent f).X 0 = cotangentSpaceSheaf f := by
  rfl

/-- The only nonzero differential of `NL_f` is the sheafified conormal map. -/
theorem naiveCotangent_d_negOne_zero {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (naiveCotangent f).d (-1) 0 = cotangentDifferential f := by
  change CochainComplex.of.d (naiveCotangentTerm f) (naiveCotangentDifferential f)
      (Int.negSucc 0) (Int.negSucc 0 + 1) = naiveCotangentDifferential f (Int.negSucc 0)
  exact CochainComplex.of_d (naiveCotangentTerm f) (naiveCotangentDifferential f) (Int.negSucc 0)

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace

/-- `NL[f]` is the naive cotangent complex of a morphism of algebraic spaces. -/
scoped[AlgebraicGeometry.AlgebraicSpace] notation3:max "NL[" f "]" =>
  Hom.naiveCotangent f

end AlgebraicGeometry.AlgebraicSpace
