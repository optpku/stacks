module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Epsilon

@[expose] public section

/-!
# Dual-number modules from square-zero endomorphisms

A square-zero endomorphism of an `R`-module determines a representation of the dual numbers.
The primary owner in this file is the resulting bundled `ModuleCat (DualNumber R)` object, so
consumers do not need to install a local module instance.
-/

universe u v

open CategoryTheory
open scoped DualNumber

namespace ModuleCat.DualNumber

variable {R : Type u} [CommRing R]
variable {X : Type v} [AddCommGroup X] [Module R X]

/-- A square-zero endomorphism satisfies the relations needed by the universal property of the
dual numbers. -/
theorem liftCondition (e : Module.End R X) (he : e.comp e = 0) :
    e * e = 0 ∧ ∀ r : R, Commute e ((Algebra.ofId R (Module.End R X)) r) := by
  constructor
  · simpa only [Module.End.mul_eq_comp] using he
  · intro r
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply, Algebra.ofId_apply]

/-- The representation of the dual numbers associated to a square-zero endomorphism. -/
@[stacks 05CS "square-zero representation"]
def representation (e : Module.End R X) (he : e.comp e = 0) :
    R[ε] →ₐ[R] Module.End R X :=
  _root_.DualNumber.lift
    ⟨(Algebra.ofId R (Module.End R X), e), liftCondition e he⟩

namespace OfSquareZero

/-- The original base-ring scalar action, named so it remains distinguishable from scalar
actions transported through a bundled square-zero module. -/
def baseSmul (r : R) (x : X) : X := r • x

/-- The dual-number action determined by a square-zero endomorphism, before bundling it as a
module-category object. -/
@[stacks 05CS "square-zero scalar action"]
def smul (e : Module.End R X) (he : e.comp e = 0) (a : R[ε]) (x : X) : X :=
  representation e he a x

end OfSquareZero

/-- The dual-number module associated to a square-zero endomorphism, bundled as a module-category
object. -/
@[stacks 05CS "square-zero module"]
def ofSquareZero (e : Module.End R X) (he : e.comp e = 0) :
    ModuleCat.{v} R[ε] :=
  @ModuleCat.of R[ε] _ X _
    (Module.compHom X (representation e he).toRingHom)

section Morphism

variable {Y : Type v} [AddCommGroup Y] [Module R Y]

/-- An `R`-linear map commuting with square-zero endomorphisms is linear for the induced
dual-number actions. -/
theorem ofSquareZeroMap_smul
    (eX : Module.End R X) (heX : eX.comp eX = 0)
    (eY : Module.End R Y) (heY : eY.comp eY = 0)
    (f : X →ₗ[R] Y) (hf : f.comp eX = eY.comp f)
    (a : R[ε]) (x : X) :
    f (OfSquareZero.smul eX heX a x) =
      OfSquareZero.smul eY heY a (f x) := by
  have hfx : f (eX x) = eY (f x) := by
    simpa only [LinearMap.comp_apply] using DFunLike.congr_fun hf x
  simp [OfSquareZero.smul, representation, _root_.DualNumber.lift_apply_apply,
    Module.End.mul_apply, Algebra.ofId_apply, hfx]

/-- A commuting linear map as a morphism between the associated dual-number modules. -/
@[stacks 05CS "morphism of square-zero modules"]
def ofSquareZeroMap
    (eX : Module.End R X) (heX : eX.comp eX = 0)
    (eY : Module.End R Y) (heY : eY.comp eY = 0)
    (f : X →ₗ[R] Y) (hf : f.comp eX = eY.comp f) :
    ofSquareZero eX heX ⟶ ofSquareZero eY heY :=
  @ModuleCat.ofHom R[ε] _ X Y
    (ofSquareZero eX heX).isAddCommGroup (ofSquareZero eX heX).isModule
    (ofSquareZero eY heY).isAddCommGroup (ofSquareZero eY heY).isModule
    (@LinearMap.mk R[ε] R[ε] _ _ (RingHom.id R[ε]) X Y
      (ofSquareZero eX heX).isAddCommGroup.toAddCommMonoid
      (ofSquareZero eY heY).isAddCommGroup.toAddCommMonoid
      (ofSquareZero eX heX).isModule (ofSquareZero eY heY).isModule
      f.toAddHom (ofSquareZeroMap_smul eX heX eY heY f hf))

/-- The morphism induced by a commuting linear map has the same underlying function. -/
@[simp]
theorem ofSquareZeroMap_apply
    (eX : Module.End R X) (heX : eX.comp eX = 0)
    (eY : Module.End R Y) (heY : eY.comp eY = 0)
    (f : X →ₗ[R] Y) (hf : f.comp eX = eY.comp f) (x : X) :
    (ofSquareZeroMap eX heX eY heY f hf).hom x = f x := rfl

end Morphism

/-- In `ofSquareZero e he`, the dual-number generator acts by `e`. -/
@[simp]
theorem eps_smul (e : Module.End R X) (he : e.comp e = 0)
    (x : ofSquareZero e he) :
    (ε : R[ε]) • x = e x := by
  change OfSquareZero.smul e he (ε : R[ε]) x = e x
  simp [OfSquareZero.smul, representation]

/-- On `ofSquareZero e he`, multiplication by `ε` is the chosen endomorphism. -/
@[simp]
theorem epsEnd_apply_ofSquareZero (e : Module.End R X) (he : e.comp e = 0)
    (x : ofSquareZero e he) :
    (epsEnd (ofSquareZero e he)).hom x = e x := by
  simpa only [epsEnd_apply] using eps_smul e he x

/-- After restriction to `R`, multiplication by `ε` on `ofSquareZero e he` is still `e`. -/
@[simp]
theorem restrictedEpsEnd_apply_ofSquareZero
    (e : Module.End R X) (he : e.comp e = 0)
    (x : restrict (ofSquareZero e he)) :
    (restrictedEpsEnd (ofSquareZero e he)).hom x = e x := by
  change OfSquareZero.smul e he (ε : R[ε]) x = e x
  simp [OfSquareZero.smul, representation]

/-- In `ofSquareZero e he`, a base scalar acts through the original `R`-module structure. -/
@[simp]
theorem inl_smul (e : Module.End R X) (he : e.comp e = 0) (r : R)
    (x : X) :
    OfSquareZero.smul e he (TrivSqZeroExt.inl r) x =
      OfSquareZero.baseSmul r x := by
  simp [OfSquareZero.smul, OfSquareZero.baseSmul, representation,
    Algebra.ofId_apply]

/-- The identity additive equivalence from the restricted square-zero module to the original
module is `R`-linear. -/
theorem restrictEquiv_map_smul (e : Module.End R X) (he : e.comp e = 0)
    (r : R) (x : restrict (ofSquareZero e he)) :
    AddEquiv.refl X (r • x) = r • AddEquiv.refl X x := by
  have hrestrict :
      (r • x : restrict (ofSquareZero e he)) =
        (algebraMap R R[ε] r) • (show ofSquareZero e he from x) :=
    ModuleCat.restrictScalars.smul_def (algebraMap R R[ε]) r x
  have hcast := congrArg
    (fun y : restrict (ofSquareZero e he) => (show X from y)) hrestrict
  calc
    AddEquiv.refl X (r • x) =
        (show X from
          (algebraMap R R[ε] r) • (show ofSquareZero e he from x)) := hcast
    _ = OfSquareZero.baseSmul r (show X from x) := by
      change OfSquareZero.smul e he (algebraMap R R[ε] r) (show X from x) =
        OfSquareZero.baseSmul r (show X from x)
      simpa only [TrivSqZeroExt.algebraMap_eq_inl] using
        inl_smul e he r (show X from x)
    _ = r • AddEquiv.refl X x := rfl

/-- Restricting a square-zero dual-number module to the base ring recovers its original module. -/
@[stacks 05CS "restriction to the base"]
noncomputable def restrictEquiv (e : Module.End R X) (he : e.comp e = 0) :
    (restrict (ofSquareZero e he) : Type v) ≃ₗ[R] X :=
  { __ := AddEquiv.refl X
    map_smul' := restrictEquiv_map_smul e he }

/-- The categorical form of `restrictEquiv`. -/
@[stacks 05CS "restriction to the base"]
noncomputable def restrictIso (e : Module.End R X) (he : e.comp e = 0) :
    restrict (ofSquareZero e he) ≅ ModuleCat.of R X :=
  (restrictEquiv e he).toModuleIso

namespace OfSquareZero

/-- A square-zero dual-number module built on a free base module remains free after restriction
to the base ring. -/
@[stacks 05CS "free after restriction"]
instance freeRestrict (e : Module.End R X) (he : e.comp e = 0)
    [Module.Free R X] : Module.Free R (restrict (ofSquareZero e he)) :=
  Module.Free.of_equiv (restrictEquiv e he).symm

end OfSquareZero

namespace Reconstruction

/-- The original dual-number action on a bundled module, named so it can be compared with the
action reconstructed from multiplication by `ε`. -/
def originalSmul (M : ModuleCat.{v} R[ε]) (a : R[ε]) (x : M) : M := a • x

/-- The dual-number action reconstructed from restricted multiplication by `ε` agrees with the
original scalar action. -/
theorem smul (M : ModuleCat.{v} R[ε]) (a : R[ε])
    (x : ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M)) :
    (a • x : ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M)) = originalSmul M a x := by
  change OfSquareZero.smul (restrictedEpsEnd M).hom
    (restrictedEpsEnd_hom_sq M) a x = originalSmul M a x
  rw [OfSquareZero.smul, representation, _root_.DualNumber.lift_apply_apply]
  change OfSquareZero.baseSmul a.fst (show restrict M from x) +
      OfSquareZero.baseSmul a.snd
        ((restrictedEpsEnd M).hom (show restrict M from x)) =
    originalSmul M a (show M from x)
  rw [restrictedEpsEnd_apply]
  unfold OfSquareZero.baseSmul originalSmul
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  simp only [TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← a.inl_fst_add_inr_snd_eq]
  rw [add_smul]
  congr 1
  rw [← mul_smul, TrivSqZeroExt.inl_mul_eq_smul,
    ← _root_.DualNumber.inr_eq_smul_eps]

/-- The identity additive equivalence used in reconstruction is linear over the dual numbers. -/
theorem map_smul (M : ModuleCat.{v} R[ε]) (a : R[ε])
    (x : ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M)) :
    AddEquiv.refl M (a • x) = a • AddEquiv.refl M x := by
  change (a • x : ofSquareZero (restrictedEpsEnd M).hom
    (restrictedEpsEnd_hom_sq M)) = originalSmul M a x
  exact smul M a x

/-- Reconstructing a dual-number module from restricted multiplication by `ε` recovers the
original module. -/
@[stacks 05CS "reconstruction from epsilon"]
noncomputable def equiv (M : ModuleCat.{v} R[ε]) :
    (ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M) : Type v) ≃ₗ[R[ε]] M :=
  { __ := AddEquiv.refl M
    map_smul' := map_smul M }

/-- Categorical form of `Reconstruction.equiv`. -/
@[stacks 05CS "reconstruction from epsilon"]
noncomputable def iso (M : ModuleCat.{v} R[ε]) :
    ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M) ≅ M :=
  (equiv M).toModuleIso

end Reconstruction

end ModuleCat.DualNumber
