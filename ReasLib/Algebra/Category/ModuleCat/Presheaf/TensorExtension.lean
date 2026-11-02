/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Actual tensor data for same-site scalar extension

Objects and restriction functions are specified tensors and tensor maps.
No right-adjoint existence certificate, chosen adjoint, or selected comparison
is used. The displayed naturality/linearity laws are ordinary Prop obligations.
This is the presheaf stage; it does not yet replace the geometric inverse image
or certify small-universe sheafification used by the existing pullback owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf
open scoped TensorProduct

noncomputable section

universe u v w z

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.PresheafTensorExtension

variable {C : Type u} [Category.{v} C]
    {R R' : Cᵒᵖ ⥤ CommRingCat.{w}} (α : R ⟶ R')

/-- The coefficient restriction is the actual ring-presheaf restriction. -/
def coefficientRestriction {U V : Cᵒᵖ} (i : U ⟶ V) :
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
    letI := (α.app U).hom.toAlgebra
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at V, the target of the semilinear restriction map.
    letI := (α.app V).hom.toAlgebra
    R'.obj U →ₛₗ[(R.map i).hom] R'.obj V := by
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
  letI := (α.app U).hom.toAlgebra
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at V, the target of the semilinear restriction map.
  letI := (α.app V).hom.toAlgebra
  refine
    { toFun := (R'.map i).hom
      map_add' := map_add (R'.map i).hom
      map_smul' := ?_ }
  intro r s
  change (R'.map i).hom ((α.app U).hom r * s) =
    (α.app V).hom ((R.map i).hom r) * (R'.map i).hom s
  rw [map_mul]
  exact congrArg (fun a : R'.obj V ↦ a * (R'.map i).hom s)
    ((NatTrans.naturality_apply α i r).symm)

variable (M : PresheafOfModules.{max w z} (ringPresheafOfComm R))

/-- Actual scalar extension at an object is the algebraic tensor product. -/
abbrev value (U : Cᵒᵖ) : ModuleCat.{max w z} (R'.obj U) :=
  (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)

/-- Actual restriction sends a tensor of coefficient and numerator to their restrictions. -/
def restrictionAdd {U V : Cᵒᵖ} (i : U ⟶ V) : value α M U →+ value α M V := by
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
  letI := (α.app U).hom.toAlgebra
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at V, the target of the semilinear restriction map.
  letI := (α.app V).hom.toAlgebra
  exact (TensorProduct.map (coefficientRestriction α i) (M.restrictₛₗ i)).toAddMonoidHom

theorem restriction_tmul {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : R'.obj U) (m : M.obj U) :
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
    letI := (α.app U).hom.toAlgebra
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at V, the target of the semilinear restriction map.
    letI := (α.app V).hom.toAlgebra
    restrictionAdd α M i (r ⊗ₜ[R.obj U] m) =
      (R'.map i).hom r ⊗ₜ[R.obj V] (show M.obj V from M.map i m) := by
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
  letI := (α.app U).hom.toAlgebra
  -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at V, the target of the semilinear restriction map.
  letI := (α.app V).hom.toAlgebra
  exact TensorProduct.map_tmul _ _ r m

set_option backward.isDefEq.respectTransparency false in
/-- This property concerns the displayed tensor map; it introduces no new map data. -/
theorem restriction_smul {U V : Cᵒᵖ} (i : U ⟶ V) (r : R'.obj U) (m : value α M U) :
    restrictionAdd α M i (r • m) = (R'.map i).hom r • restrictionAdd α M i m := by
  letI := (α.app U).hom.toAlgebra
  letI := (α.app V).hom.toAlgebra
  change R'.obj U ⊗[R.obj U] M.obj U at m
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    calc
      restrictionAdd α M i (r • (s ⊗ₜ[R.obj U] n)) =
          (R'.map i).hom (r * s) ⊗ₜ[R.obj V] (M.map i n : M.obj V) :=
        restriction_tmul α M i (r * s) n
      _ = ((R'.map i).hom r * (R'.map i).hom s) ⊗ₜ[R.obj V]
          (M.map i n : M.obj V) := by rw [map_mul]
      _ = (R'.map i).hom r • restrictionAdd α M i (s ⊗ₜ[R.obj U] n) :=
        (congrArg (fun x : value α M V ↦ (R'.map i).hom r • x)
          (restriction_tmul α M i s n)).symm
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]

/-- The tensor map with its scalar-linearity certificate. -/
def restriction {U V : Cᵒᵖ} (i : U ⟶ V) :
    value α M U ⟶ (ModuleCat.restrictScalars (R'.map i).hom).obj (value α M V) :=
  ModuleCat.ofHom (X := value α M U)
    (Y := (ModuleCat.restrictScalars (R'.map i).hom).obj (value α M V))
    { toFun := restrictionAdd α M i
      map_add' := (restrictionAdd α M i).map_add
      map_smul' := restriction_smul α M i }

set_option backward.isDefEq.respectTransparency false in
/-- Same-site extension as explicit presheaf data, with diagram laws proved on pure tensors. -/
def presheaf : PresheafOfModules.{max w z} (ringPresheafOfComm R') where
  obj := value α M
  map := restriction α M
  map_id U := by
    letI := (α.app U).hom.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change restrictionAdd α M (𝟙 U) x = x
    change R'.obj U ⊗[R.obj U] M.obj U at x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul r m =>
      exact (restriction_tmul α M (𝟙 U) r m).trans
        (congrArg₂ (fun (s : R'.obj U) (n : M.obj U) ↦ s ⊗ₜ[R.obj U] n)
          (CategoryTheory.congr_fun (R'.map_id U) r)
          (CategoryTheory.congr_fun (M.map_id U) m))
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp := by
    intro U V W i j
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    letI := (α.app W).hom.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change restrictionAdd α M (i ≫ j) x =
      restrictionAdd α M j (restrictionAdd α M i x)
    change R'.obj U ⊗[R.obj U] M.obj U at x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      calc
        restrictionAdd α M (i ≫ j) (r ⊗ₜ[R.obj U] m) =
            (R'.map (i ≫ j)).hom r ⊗ₜ[R.obj W] (M.map (i ≫ j) m : M.obj W) :=
          restriction_tmul α M (i ≫ j) r m
        _ = (R'.map j).hom ((R'.map i).hom r) ⊗ₜ[R.obj W]
            (M.map j (M.map i m) : M.obj W) :=
          congrArg₂ (fun (s : R'.obj W) (n : M.obj W) ↦ s ⊗ₜ[R.obj W] n)
            (CategoryTheory.congr_fun (R'.map_comp i j) r) (M.map_comp_apply i j m)
        _ = restrictionAdd α M j
            ((R'.map i).hom r ⊗ₜ[R.obj V] (M.map i m : M.obj V)) :=
          (restriction_tmul α M j ((R'.map i).hom r) (M.map i m)).symm
        _ = restrictionAdd α M j (restrictionAdd α M i (r ⊗ₜ[R.obj U] m)) :=
          congrArg (restrictionAdd α M j) (restriction_tmul α M i r m).symm
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Module morphisms act by the actual objectwise tensor maps. -/
def mapApp {M N : PresheafOfModules.{max w z} (ringPresheafOfComm R)} (f : M ⟶ N)
    (U : Cᵒᵖ) : (value α M U) ⟶ (value α N U) :=
  (ModuleCat.extendScalars (α.app U).hom).map (f.app U)

set_option backward.isDefEq.respectTransparency false in
def map {M N : PresheafOfModules.{max w z} (ringPresheafOfComm R)} (f : M ⟶ N) :
    presheaf α M ⟶ presheaf α N where
  app U := mapApp α f U
  naturality := by
    intro U V i
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change mapApp α f V (restrictionAdd α M i x) =
      restrictionAdd α N i (mapApp α f U x)
    change R'.obj U ⊗[R.obj U] M.obj U at x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      calc
        mapApp α f V (restrictionAdd α M i (r ⊗ₜ[R.obj U] m)) =
            mapApp α f V ((R'.map i).hom r ⊗ₜ[R.obj V] (M.map i m : M.obj V)) :=
          congrArg (mapApp α f V) (restriction_tmul α M i r m)
        _ = (R'.map i).hom r ⊗ₜ[R.obj V] f.app V (M.map i m) := rfl
        _ = (R'.map i).hom r ⊗ₜ[R.obj V] (N.map i (f.app U m) : N.obj V) :=
          congrArg (fun n : N.obj V ↦ (R'.map i).hom r ⊗ₜ[R.obj V] n)
            (PresheafOfModules.naturality_apply f i m)
        _ = restrictionAdd α N i (r ⊗ₜ[R.obj U] f.app U m) :=
          (restriction_tmul α N i r (f.app U m)).symm
        _ = restrictionAdd α N i (mapApp α f U (r ⊗ₜ[R.obj U] m)) := rfl
    | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- The specified tensor scalar-extension functor, not a chosen adjoint. -/
def functor : PresheafOfModules.{max w z} (ringPresheafOfComm R) ⥤
    PresheafOfModules.{max w z} (ringPresheafOfComm R') where
  obj := presheaf α
  map := map α
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_id (M.obj U)
  map_comp := by
    intro M N P f g
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_comp (f.app U) (g.app U)

/-- Evaluation on `1 tensor m` is the actual forward Hom correspondence. -/
def toRestrictionApp {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : presheaf α M ⟶ N) (U : Cᵒᵖ) :
    M.obj U ⟶ (ModuleCat.restrictScalars (α.app U).hom).obj (N.obj U) :=
  (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _ (f.app U)

def fromRestrictionApp {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : M ⟶ (PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap α)).obj N) (U : Cᵒᵖ) :
    (presheaf α M).obj U ⟶ N.obj U :=
  ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm (f.app U)

/-- The forward Hom correspondence evaluates the supplied map on `1 tensor m`. -/
theorem toRestrictionApp_apply {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : presheaf α M ⟶ N) (U : Cᵒᵖ) (m : M.obj U) :
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
    letI := (α.app U).hom.toAlgebra
    toRestrictionApp α f U m = f.app U ((1 : R'.obj U) ⊗ₜ[R.obj U] m) := rfl

/-- The inverse Hom correspondence applies the coefficient to the supplied numerator map. -/
theorem fromRestrictionApp_tmul {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : M ⟶ (PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap α)).obj N)
    (U : Cᵒᵖ) (r : R'.obj U) (m : M.obj U) :
    -- Local instance justification (defeq pin): Use the scalar action induced by the supplied coefficient map α at U in this tensor product and its generator formula.
    letI := (α.app U).hom.toAlgebra
    fromRestrictionApp α f U (r ⊗ₜ[R.obj U] m) = r • (show N.obj U from f.app U m) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on `1 tensor m` is the actual forward Hom correspondence. -/
def toRestriction {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : presheaf α M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap α)).obj N where
  app U := toRestrictionApp α f U
  naturality := by
    intro U V i
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    ext m
    change toRestrictionApp α f V (M.map i m) =
      N.map i (toRestrictionApp α f U m)
    rw [toRestrictionApp_apply, toRestrictionApp_apply]
    have h := PresheafOfModules.naturality_apply f i ((1 : R'.obj U) ⊗ₜ[R.obj U] m)
    change f.app V (restrictionAdd α M i ((1 : R'.obj U) ⊗ₜ[R.obj U] m)) = _ at h
    simpa only [restriction_tmul, map_one] using h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse Hom correspondence uses the algebraic tensor universal property objectwise. -/
def fromRestriction {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : M ⟶ (PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap α)).obj N) :
    presheaf α M ⟶ N where
  app U := fromRestrictionApp α f U
  naturality := by
    intro U V i
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change fromRestrictionApp α f V (restrictionAdd α M i x) =
      N.map i (fromRestrictionApp α f U x)
    change R'.obj U ⊗[R.obj U] M.obj U at x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r m =>
      rw [restriction_tmul, fromRestrictionApp_tmul, fromRestrictionApp_tmul, N.map_smul]
      congr 1
      exact PresheafOfModules.naturality_apply f i m
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Both inverse functions are already specified; their inverse laws are the proved algebraic ones. -/
def homEquiv (M : PresheafOfModules.{max w z} (ringPresheafOfComm R))
    (N : PresheafOfModules.{max w z} (ringPresheafOfComm R')) :
    (presheaf α M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap α)).obj N) where
  toFun := toRestriction α
  invFun := fromRestriction α
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm_apply_apply (f.app U)
  right_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).apply_symm_apply (f.app U)

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction data use the specified functor and specified tensor Hom maps. -/
def adjunction : functor α ⊣
    PresheafOfModules.restrictScalars.{max w z} (PresheafOfModules.presheafStructureMap α) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv α
      homEquiv_naturality_left_symm := by
        intro M N P f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv_naturality_left_symm
          (f.app U) (g.app U)
      homEquiv_naturality_right := by
        intro M N P f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv_naturality_right
          (f.app U) (g.app U) }

/-- In the coefficient universe, the two concrete same-site tensor extensions
are canonically isomorphic through their specified adjunctions. The mixed-universe
functor above remains available without this specialization. -/
def sameUniverseComparison :
    PresheafOfModules.SameSiteTensorExtension.functor α ≅ functor.{u, v, w, w} α :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.SameSiteTensorExtension.adjunction α) (adjunction α)

/-- The comparison identifies the two specified tensor-adjunction units. -/
theorem sameUniverseComparison_unit
    (M : PresheafOfModules.{w} (ringPresheafOfComm R)) :
    (PresheafOfModules.SameSiteTensorExtension.adjunction α).unit.app M ≫
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.SameSiteTensorExtension.ringMap α)).map
            ((sameUniverseComparison α).hom.app M) =
      (adjunction α).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (PresheafOfModules.SameSiteTensorExtension.adjunction α) (adjunction α) M

set_option backward.isDefEq.respectTransparency false in
/-- On each section, the canonical comparison is the identity tensor map. -/
@[simp]
theorem sameUniverseComparison_hom_app_app
    (M : PresheafOfModules.{w} (ringPresheafOfComm R)) (U : Cᵒᵖ) :
    ((sameUniverseComparison α).hom.app M).app U =
      𝟙 ((ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)) := by
  letI := (α.app U).hom.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h := congrArg (fun f ↦ f.app U m) (sameUniverseComparison_unit α M)
  change ((sameUniverseComparison α).hom.app M).app U
    ((1 : R'.obj U) ⊗ₜ[R.obj U] m) = (1 : R'.obj U) ⊗ₜ[R.obj U] m at h
  exact h

/-- The comparison preserves every tensor element, not only pure tensors. -/
@[simp]
theorem sameUniverseComparison_app_apply
    (M : PresheafOfModules.{w} (ringPresheafOfComm R)) (U : Cᵒᵖ)
    (m : (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)) :
    (((sameUniverseComparison α).hom.app M).app U) m = m :=
  congrArg (fun f ↦ f m) (sameUniverseComparison_hom_app_app α M U)

/-- The inverse comparison also preserves every tensor element. -/
@[simp]
theorem sameUniverseComparison_inv_app_apply
    (M : PresheafOfModules.{w} (ringPresheafOfComm R)) (U : Cᵒᵖ)
    (m : (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)) :
    (((sameUniverseComparison α).inv.app M).app U) m = m := by
  have h := congrArg (fun f ↦ f.app U m) ((sameUniverseComparison α).hom_inv_id_app M)
  change ((sameUniverseComparison α).inv.app M).app U
    (((sameUniverseComparison α).hom.app M).app U m) = m at h
  simpa only [sameUniverseComparison_app_apply] using h

/-- A concrete witness now supplies this presheaf-level right-adjoint certificate. -/
theorem restrictScalars_isRightAdjoint :
    (PresheafOfModules.restrictScalars.{max w z}
      (PresheafOfModules.presheafStructureMap α)).IsRightAdjoint :=
  (adjunction α).isRightAdjoint

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.PresheafTensorExtension
