/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.SectionTensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Inverse
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Restriction of kernels, tensors, and inverse modules to schemes -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalCategory.isInvertibleObject
open CategoryTheory.ExactPairing

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- A section of a restricted scheme module, viewed on its corresponding étale chart. -/
def ofRestrictSection {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (s : ((restrictToScheme U).obj A).val.obj V) :
    A.val.obj (op (RestrictToScheme.siteObject U V.unop)) :=
  RestrictToScheme.sectionEquiv U A V.unop s

/-- A section on an open étale chart, viewed as a section of the restricted scheme module. -/
def toRestrictSection {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (s : A.val.obj (op (RestrictToScheme.siteObject U V.unop))) :
    ((restrictToScheme U).obj A).val.obj V :=
  (RestrictToScheme.sectionEquiv U A V.unop).symm s

theorem ofRestrictSection_add {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (x y : ((restrictToScheme U).obj A).val.obj V) :
    ofRestrictSection A (x + y) = ofRestrictSection A x + ofRestrictSection A y := rfl

theorem toRestrictSection_add {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (x y : A.val.obj (op (RestrictToScheme.siteObject U V.unop))) :
    toRestrictSection A (x + y) = toRestrictSection A x + toRestrictSection A y := rfl

theorem asCommSection_add {X : AlgebraicSpace S} (A : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ} (x y : A.val.obj V) :
    RelativeProj.asCommSection A (x + y) =
      RelativeProj.asCommSection A x + RelativeProj.asCommSection A y := rfl

theorem ofCommSection_add {X : AlgebraicSpace S} (A : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ} (x y : ((toCommModules X).obj A).val.obj V) :
    RelativeProj.ofCommSection A (x + y) =
      RelativeProj.ofCommSection A x + RelativeProj.ofCommSection A y := rfl

theorem ofRestrictSection_smul {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (r : U.left.sheaf.obj.obj V)
    (x : ((restrictToScheme U).obj A).val.obj V) :
    ofRestrictSection A (r • x) =
      (((RestrictToScheme.unitMap U).val.app V).hom r) • ofRestrictSection A x := rfl

theorem toRestrictSection_smul {U : Over S} (A : (ofOver U).Modules)
    {V : U.left.Opensᵒᵖ} (r : U.left.sheaf.obj.obj V)
    (x : A.val.obj (op (RestrictToScheme.siteObject U V.unop))) :
    toRestrictSection A ((((RestrictToScheme.unitMap U).val.app V).hom r) • x) =
      r • toRestrictSection A x := rfl

theorem asCommSection_smul {X : AlgebraicSpace S} (A : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ} (r : (commStructureSheaf X).obj.obj V) (x : A.val.obj V) :
    RelativeProj.asCommSection A (r • x) = r • RelativeProj.asCommSection A x := rfl

theorem ofCommSection_smul {X : AlgebraicSpace S} (A : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ} (r : (commStructureSheaf X).obj.obj V)
    (x : ((toCommModules X).obj A).val.obj V) :
    RelativeProj.ofCommSection A (r • x) = r • RelativeProj.ofCommSection A x := rfl

theorem ofRestrictSection_map {U : Over S} (A : (ofOver U).Modules)
    {V W : U.left.Opensᵒᵖ} (i : V ⟶ W) (x : ((restrictToScheme U).obj A).val.obj V) :
    ofRestrictSection A (((((restrictToScheme U).obj A).val.map i).hom) x) =
      (A.val.map ((SmallEtale.openChart (tautologicalChart U) ⋙
        SmallEtale.toPresentation (ofOver U)).op.map i)).hom (ofRestrictSection A x) := rfl

theorem toRestrictSection_map {U : Over S} (A : (ofOver U).Modules)
    {V W : U.left.Opensᵒᵖ} (i : V ⟶ W)
    (x : A.val.obj (op (RestrictToScheme.siteObject U V.unop))) :
    ((((restrictToScheme U).obj A).val.map i).hom) (toRestrictSection A x) =
      toRestrictSection A (V := W) ((A.val.map
        ((SmallEtale.openChart (tautologicalChart U) ⋙
          SmallEtale.toPresentation (ofOver U)).op.map i)).hom x) := rfl

theorem asCommSection_map {X : AlgebraicSpace S} (A : X.Modules)
    {V W : (smallEtaleSite X)ᵒᵖ} (i : V ⟶ W) (x : A.val.obj V) :
    RelativeProj.asCommSection A (U := W) ((A.val.map i).hom x) =
      ((((toCommModules X).obj A).val.map i).hom) (RelativeProj.asCommSection A x) := rfl

theorem ofCommSection_map {X : AlgebraicSpace S} (A : X.Modules)
    {V W : (smallEtaleSite X)ᵒᵖ} (i : V ⟶ W)
    (x : ((toCommModules X).obj A).val.obj V) :
    (A.val.map i).hom (RelativeProj.ofCommSection A x) =
      RelativeProj.ofCommSection A (((((toCommModules X).obj A).val.map i).hom) x) := rfl

/-- Kernel comparison for restriction of modules from `ofOver U` to the underlying scheme. -/
def restrictKernelComparison {U : Over S} {A B : (ofOver U).Modules} (f : A ⟶ B) :
    (restrictToScheme U).obj (kernel f) ⟶ kernel ((restrictToScheme U).map f) :=
  kernelComparison f (restrictToScheme U)

/-- Restriction of modules preserves kernels of module morphisms. -/
instance instIsIso_restrictKernelComparison {U : Over S} {A B : (ofOver U).Modules}
    (f : A ⟶ B) :
    IsIso (restrictKernelComparison f) := by
  letI := (RestrictToScheme.extensionAdjunction U).isRightAdjoint
  change IsIso (kernelComparison f (restrictToScheme U))
  infer_instance

theorem commTensorSection_add_right {X : AlgebraicSpace S} (A B : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ}
    (x : ((toCommModules X).obj A).val.obj V)
    (y y' : ((toCommModules X).obj B).val.obj V) :
    RelativeProj.commTensorSection A B x (y + y') =
      RelativeProj.commTensorSection A B x y + RelativeProj.commTensorSection A B x y' := by
  unfold RelativeProj.commTensorSection RelativeProj.commPointwiseTensor
  erw [TensorProduct.tmul_add, map_add, map_add]

theorem commTensorSection_add_left {X : AlgebraicSpace S} (A B : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ}
    (x x' : ((toCommModules X).obj A).val.obj V)
    (y : ((toCommModules X).obj B).val.obj V) :
    RelativeProj.commTensorSection A B (x + x') y =
      RelativeProj.commTensorSection A B x y + RelativeProj.commTensorSection A B x' y := by
  unfold RelativeProj.commTensorSection RelativeProj.commPointwiseTensor
  erw [TensorProduct.add_tmul, map_add, map_add]

theorem commTensorSection_smul_right {X : AlgebraicSpace S} (A B : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ}
    (x : ((toCommModules X).obj A).val.obj V) (r : (commStructureSheaf X).obj.obj V)
    (y : ((toCommModules X).obj B).val.obj V) :
    RelativeProj.commTensorSection A B x (r • y) =
      r • RelativeProj.commTensorSection A B x y := by
  unfold RelativeProj.commTensorSection RelativeProj.commPointwiseTensor
  erw [TensorProduct.tmul_smul (R := (commStructureSheaf X).obj.obj V) r x y,
    map_smul, map_smul]
  rfl

theorem commTensorSection_smul_left {X : AlgebraicSpace S} (A B : X.Modules)
    {V : (smallEtaleSite X)ᵒᵖ} (r : (commStructureSheaf X).obj.obj V)
    (x : ((toCommModules X).obj A).val.obj V)
    (y : ((toCommModules X).obj B).val.obj V) :
    RelativeProj.commTensorSection A B (r • x) y =
      r • RelativeProj.commTensorSection A B x y := by
  unfold RelativeProj.commTensorSection RelativeProj.commPointwiseTensor
  erw [← TensorProduct.smul_tmul' (R := (commStructureSheaf X).obj.obj V) r x y,
    map_smul, map_smul]
  rfl

theorem commTensorSection_map {X : AlgebraicSpace S} (A B : X.Modules)
    {V W : (smallEtaleSite X)ᵒᵖ} (i : V ⟶ W)
    (x : ((toCommModules X).obj A).val.obj V)
    (y : ((toCommModules X).obj B).val.obj V) :
    (((toCommModules X).obj (A ⊗ B)).val.map i).hom
        (RelativeProj.commTensorSection A B x y) =
      RelativeProj.commTensorSection A B
        ((((toCommModules X).obj A).val.map i).hom x)
        ((((toCommModules X).obj B).val.map i).hom y) := by
  unfold RelativeProj.commTensorSection RelativeProj.commPointwiseTensor
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rfl

set_option maxHeartbeats 400000 in
theorem restrictTensorSection_map {U : Over S} (A B : (ofOver U).Modules)
    {V W : U.left.Opensᵒᵖ} (i : V ⟶ W)
    (x : ((restrictToScheme U).obj A).val.obj V)
    (y : ((restrictToScheme U).obj B).val.obj V) :
    ((((restrictToScheme U).obj (A ⊗ B)).val.map i).hom)
        (toRestrictSection (A ⊗ B)
          (RelativeProj.ofCommSection (A ⊗ B)
            (RelativeProj.commTensorSection A B
              (RelativeProj.asCommSection A (ofRestrictSection A x))
              (RelativeProj.asCommSection B (ofRestrictSection B y))))) =
      toRestrictSection (A ⊗ B)
        (RelativeProj.ofCommSection (A ⊗ B)
          (RelativeProj.commTensorSection A B
            (RelativeProj.asCommSection A
              (ofRestrictSection A (((((restrictToScheme U).obj A).val.map i).hom) x)))
            (RelativeProj.asCommSection B
              (ofRestrictSection B (((((restrictToScheme U).obj B).val.map i).hom) y))))) := by
  let j := (SmallEtale.openChart (tautologicalChart U) ⋙
    SmallEtale.toPresentation (ofOver U)).op.map i
  erw [toRestrictSection_map (A ⊗ B) i, ofCommSection_map (A ⊗ B) j,
    commTensorSection_map A B j, ofRestrictSection_map A i, ofRestrictSection_map B i,
    asCommSection_map A j, asCommSection_map B j]
  rfl

/-- The sectionwise bilinear map presenting restriction of a tensor product. -/
def restrictTensorBilinear {U : Over S} (A B : (ofOver U).Modules) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u, u} U.left.sheaf
      ((restrictToScheme U).obj A) ((restrictToScheme U).obj B)
      ((restrictToScheme U).obj (A ⊗ B)) where
  app V :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            toRestrictSection (A ⊗ B)
              (RelativeProj.ofCommSection (A ⊗ B)
                (RelativeProj.commTensorSection A B
                  (RelativeProj.asCommSection A (ofRestrictSection A x))
                  (RelativeProj.asCommSection B (ofRestrictSection B y))))
          map_add' := fun y y' ↦ by
            simp only [ofRestrictSection_add, asCommSection_add,
              commTensorSection_add_right, ofCommSection_add, toRestrictSection_add]
          map_smul' := fun r y ↦ by
            simp only [ofRestrictSection_smul, RingHom.id_apply]
            erw [asCommSection_smul, commTensorSection_smul_right,
              ofCommSection_smul, toRestrictSection_smul] }
      map_add' := fun x x' ↦ LinearMap.ext fun y ↦ by
        simp only [ofRestrictSection_add, asCommSection_add,
          commTensorSection_add_left, ofCommSection_add, toRestrictSection_add,
          LinearMap.add_apply]
        rfl
      map_smul' := fun r x ↦ LinearMap.ext fun y ↦ by
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        simp only [ofRestrictSection_smul, RingHom.id_apply, LinearMap.smul_apply]
        erw [asCommSection_smul, commTensorSection_smul_left,
          ofCommSection_smul, toRestrictSection_smul]
        rfl }
  naturality i x y := restrictTensorSection_map A B i x y

/-- The lax comparison `restrict A ⊗ restrict B ⟶ restrict(A ⊗ B)`. -/
def restrictTensorLax {U : Over S} (A B : (ofOver U).Modules) :
    ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) ⟶
      (restrictToScheme U).obj (A ⊗ B) :=
  (restrictTensorBilinear A B).hom

/-- On quasi-coherent inputs the restriction-tensor comparison is bijective on sections. -/
theorem restrictTensorLax_bijective {U : Over S} (A B : (ofOver U).Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] (V : U.left.Opensᵒᵖ) :
    Function.Bijective ((restrictTensorLax A B).val.app V).hom := sorry

/-- Restriction of the tensor product of quasi-coherent modules agrees with the tensor
product of the restrictions, using the actual section preimages of the comparison. -/
def restrictTensorIso {U : Over S} (A B : (ofOver U).Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] :
    ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) ≅
      (restrictToScheme U).obj (A ⊗ B) :=
  SheafOfModules.isoOfBijective (restrictTensorLax A B) (restrictTensorLax_bijective A B)

/-- The restriction-tensor comparison is an isomorphism on quasi-coherent modules. -/
instance instIsIso_restrictTensorLax {U : Over S} (A B : (ofOver U).Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] : IsIso (restrictTensorLax A B) :=
  (restrictTensorIso A B).isIso_hom

/-- The oplax comparison `restrict(A ⊗ B) ⟶ restrict A ⊗ restrict B`. -/
def restrictTensorOplax {U : Over S} (A B : (ofOver U).Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] :
    (restrictToScheme U).obj (A ⊗ B) ⟶
      ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) :=
  (restrictTensorIso A B).inv

/-- Restriction of the monoidal unit. -/
def restrictMonoidalUnitIso (U : Over S) :
    (restrictToScheme U).obj (𝟙_ (ofOver U).Modules) ≅ 𝟙_ U.left.Modules :=
  (restrictToScheme U).mapIso (PullbackTensor.structureUnitIso (ofOver U)).symm ≪≫
    (SheafOfModules.isoOfBijective (RestrictToScheme.unitMap U)
      (fun V ↦ ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.forget U.left.ringCatSheaf ⋙
          PresheafOfModules.evaluation U.left.ringCatSheaf.obj V).map
            (RestrictToScheme.unitMap U)))).symm ≪≫
    RingedSpace.unitIsoTensorUnit U.left.toRingedSpace

/-- The image pairing of an invertible module under restriction to the underlying scheme. -/
@[implicit_reducible]
def restrictImagePairing {U : Over S} (L : (ofOver U).Modules) [isInvertibleObject L] :
    ExactPairing ((restrictToScheme U).obj L)
      ((restrictToScheme U).obj (inverse L)) where
  coevaluation' :=
    (restrictMonoidalUnitIso U).inv ≫
      (restrictToScheme U).map (exactPairing L).coevaluation' ≫
        restrictTensorOplax L (inverse L)
  evaluation' :=
    restrictTensorLax (inverse L) L ≫
      (restrictToScheme U).map (exactPairing L).evaluation' ≫
        (restrictMonoidalUnitIso U).hom
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- Restriction of a chosen tensor inverse compared with the chosen inverse of the restriction. -/
def restrictInverseComparison {U : Over S} (L : (ofOver U).Modules)
    [isInvertibleObject L]
    [isInvertibleObject ((restrictToScheme U).obj L)] :
    (restrictToScheme U).obj (inverse L) ⟶ inverse ((restrictToScheme U).obj L) :=
  (rightDualIso (restrictImagePairing L)
      (exactPairing ((restrictToScheme U).obj L))).hom

/-- The restriction comparison of chosen inverses is an isomorphism. -/
instance instIsIso_restrictInverseComparison {U : Over S} (L : (ofOver U).Modules)
    [isInvertibleObject L]
    [isInvertibleObject ((restrictToScheme U).obj L)] :
    IsIso (restrictInverseComparison L) := by
  dsimp only [restrictInverseComparison]
  infer_instance

end AlgebraicGeometry.AlgebraicSpace.Modules
