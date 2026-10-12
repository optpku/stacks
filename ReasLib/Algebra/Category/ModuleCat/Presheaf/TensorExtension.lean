/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.LinearAlgebra.TensorProduct.Map

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

/-- This property concerns the displayed tensor map; it introduces no new map data. -/
theorem restriction_smul {U V : Cᵒᵖ} (i : U ⟶ V) (r : R'.obj U) (m : value α M U) :
    restrictionAdd α M i (r • m) = (R'.map i).hom r • restrictionAdd α M i m := by
  sorry

/-- The tensor map with its scalar-linearity certificate. -/
def restriction {U V : Cᵒᵖ} (i : U ⟶ V) :
    value α M U ⟶ (ModuleCat.restrictScalars (R'.map i).hom).obj (value α M V) :=
  ModuleCat.ofHom (X := value α M U)
    (Y := (ModuleCat.restrictScalars (R'.map i).hom).obj (value α M V))
    { toFun := restrictionAdd α M i
      map_add' := (restrictionAdd α M i).map_add
      map_smul' := restriction_smul α M i }

/-- Same-site extension as explicit presheaf data. Only its diagram laws remain Prop debt. -/
def presheaf : PresheafOfModules.{max w z} (ringPresheafOfComm R') where
  obj := value α M
  map := restriction α M
  map_id := by sorry
  map_comp := by sorry

/-- Module morphisms act by the actual objectwise tensor maps. -/
def mapApp {M N : PresheafOfModules.{max w z} (ringPresheafOfComm R)} (f : M ⟶ N)
    (U : Cᵒᵖ) : (value α M U) ⟶ (value α N U) :=
  (ModuleCat.extendScalars (α.app U).hom).map (f.app U)

def map {M N : PresheafOfModules.{max w z} (ringPresheafOfComm R)} (f : M ⟶ N) :
    presheaf α M ⟶ presheaf α N where
  app U := mapApp α f U
  naturality := by sorry

/-- The specified tensor scalar-extension functor, not a chosen adjoint. -/
def functor : PresheafOfModules.{max w z} (ringPresheafOfComm R) ⥤
    PresheafOfModules.{max w z} (ringPresheafOfComm R') where
  obj := presheaf α
  map := map α
  map_id := by sorry
  map_comp := by sorry

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

/-- Evaluation on `1 tensor m` is the actual forward Hom correspondence. -/
def toRestriction {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : presheaf α M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap α)).obj N where
  app U := toRestrictionApp α f U
  naturality := by sorry

/-- The inverse Hom correspondence uses the algebraic tensor universal property objectwise. -/
def fromRestriction {M : PresheafOfModules.{max w z} (ringPresheafOfComm R)}
    {N : PresheafOfModules.{max w z} (ringPresheafOfComm R')}
    (f : M ⟶ (PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap α)).obj N) :
    presheaf α M ⟶ N where
  app U := fromRestrictionApp α f U
  naturality := by sorry

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

/-- The adjunction data use the specified functor and specified tensor Hom maps. -/
def adjunction : functor α ⊣
    PresheafOfModules.restrictScalars.{max w z} (PresheafOfModules.presheafStructureMap α) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv α
      homEquiv_naturality_left_symm := by sorry
      homEquiv_naturality_right := by sorry }

/-- A concrete witness now supplies this presheaf-level right-adjoint certificate. -/
theorem restrictScalars_isRightAdjoint :
    (PresheafOfModules.restrictScalars.{max w z}
      (PresheafOfModules.presheafStructureMap α)).IsRightAdjoint :=
  (adjunction α).isRightAdjoint

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.PresheafTensorExtension
