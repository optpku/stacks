/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import stacks_project.Chap66.Lemma_66_28_1_Hom

/-!
# Naive cotangent complexes of morphisms of algebraic spaces

The naive cotangent complex `NL_f` of a morphism of algebraic spaces is the two-term complex of
`𝒪_X`-modules on `X_étale` obtained by sheafifying the objectwise naive cotangent complex of the
inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of `f^♯`. This is the algebraic-space specialization of
Modules on Sites, Definition 18.35.4, along `f_small`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Algebra Algebra.Extension Algebra.Generators
open MvPolynomial
open scoped ZeroObject

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

/-- The algebra homomorphism of canonical presentations induced by restriction along `i`. -/
def presentationAlgHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :=
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i is the coefficient algebra of presentationAlgHom, not a global Algebra.
  letI := inverseImageRestrictionAlgebra f i
  ({ presentationRingHom f i with
      commutes' := fun _ ↦ sorry } :
    MvPolynomial ((commStructureSheaf X).obj.obj U)
        ((commInverseImageStructureSheaf f).obj.obj U) →ₐ[
          (commInverseImageStructureSheaf f).obj.obj U]
      MvPolynomial ((commStructureSheaf X).obj.obj V)
        ((commInverseImageStructureSheaf f).obj.obj V))

/-- Restriction of the objectwise conormal module of the canonical presentation. -/
def cotangentObj_map {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    cotangentObj f U ⟶
      (ModuleCat.restrictScalars
        (((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
        (cotangentObj f V) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at U for Cotangent.of.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): objectwise algebra of f^♯ at V for the target kernel.
  letI := inverseImageAlgebra f V
  -- Local instance justification (noncanonical choice): restriction of f⁻¹𝒪_Y along i for presentationAlgHom.
  letI := inverseImageRestrictionAlgebra f i
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj U))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation f U).ker (presentation f V).ker
            (presentationAlgHom f i) sorry
            (Cotangent.val (P := (presentation f U).toExtension) x))
      map_add' := sorry
      map_smul' := sorry }

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
  letI := (sorry : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V))
  -- Local instance justification (noncanonical choice): scalar tower of 𝒪_X restriction from U to V, needed by Extension.Hom.
  letI := (sorry : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U)
      ((commStructureSheaf X).obj.obj V))
  ({ toRingHom := presentationRingHom f i
     toRingHom_algebraMap := fun _ ↦ sorry
     algebraMap_toRingHom := fun _ ↦ sorry } :
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
  letI := (sorry : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj V)
      ((commStructureSheaf X).obj.obj V))
  -- Local instance justification (noncanonical choice): scalar tower of 𝒪_X restriction from U to V, needed by CotangentSpace.map.
  letI := (sorry : IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj U)
      ((commStructureSheaf X).obj.obj U)
      ((commStructureSheaf X).obj.obj V))
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj U))
    (CotangentSpace.map (presentationRestrictHom f i))

/-- The presheaf of conormal modules of the canonical presentations of `f^♯`. -/
def cotangentPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) where
  obj := cotangentObj f
  map := cotangentObj_map f
  map_id := sorry
  map_comp := sorry

/-- The presheaf of base-changed presentation differentials of `f^♯`. -/
def cotangentSpacePresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) where
  obj := cotangentSpaceObj f
  map := cotangentSpaceObj_map f
  map_id := sorry
  map_comp := sorry

/-- The zero presheaf of `𝒪_X`-modules on the small étale site. -/
def zeroModulePresheaf (X : AlgebraicSpace S) :
    PresheafOfModules.{u} (structureSheaf X).obj where
  obj _ := 0
  map _ := 0
  map_id := sorry
  map_comp := sorry

/-- The objectwise conormal differential of the canonical presentation of `f^♯`. -/
def cotangentComplex_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentObj f U ⟶ cotangentSpaceObj f U :=
  -- Local instance justification (noncanonical choice): algebra `f⁻¹𝒪_Y(U) → 𝒪_X(U)`.
  letI := inverseImageAlgebra f U
  ModuleCat.ofHom (Extension.cotangentComplex (presentation f U).toExtension)

/-- The presheaf morphism `I / I ^ 2 ⟶ 𝒪_X ⊗ Ω(P / f⁻¹𝒪_Y)` of canonical presentations. -/
def cotangentDifferentialPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    cotangentPresheaf f ⟶ cotangentSpacePresheaf f where
  app := cotangentComplex_app f
  naturality := sorry

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
    (zeroModulePresheaf X)

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
    naiveCotangentDifferential f n ≫ naiveCotangentDifferential f (n + 1) = 0 :=
  sorry

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
    (naiveCotangent f).X (-1) = cotangentSheaf f :=
  sorry

/-- The degree `0` term of `NL_f` is the sheafification of `𝒪_X ⊗ Ω(P / f⁻¹𝒪_Y)`. -/
theorem naiveCotangent_X_zero {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (naiveCotangent f).X 0 = cotangentSpaceSheaf f :=
  sorry

/-- The only nonzero differential of `NL_f` is the sheafified conormal map. -/
theorem naiveCotangent_d_negOne_zero {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (naiveCotangent f).d (-1) 0 = cotangentDifferential f :=
  sorry

/-- `NL_f` is the Modules-on-Sites naive cotangent complex of
`commInverseImageStructureSheafMap f`, and forgetting commutativity of that map recovers
`(ringedToposHom f).structureMap`. -/
theorem naiveCotangent_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    naiveCotangent f =
        CochainComplex.of (naiveCotangentTerm f) (naiveCotangentDifferential f)
          (naiveCotangentDifferential_sq_zero f) ∧
      (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (commInverseImageStructureSheafMap f) =
        eqToHom (commInverseImageStructureSheaf_forget f) ≫
          (ringedToposHom f).structureMap ≫
          eqToHom (commStructureSheaf_forget X).symm :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace

/-- `NL[f]` is the naive cotangent complex of a morphism of algebraic spaces. -/
scoped[AlgebraicGeometry.AlgebraicSpace] notation3:max "NL[" f "]" =>
  Hom.naiveCotangent f

end AlgebraicGeometry.AlgebraicSpace
