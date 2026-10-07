module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.TransferInstance

@[expose] public section

open scoped TensorProduct
open CategoryTheory TensorProduct

universe u v

namespace Connection

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A']
variable {B' : Type v} [CommRing B'] [Algebra A' B'] [Algebra B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω'] [IsScalarTower A' B' Ω']
variable [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- Extension of scalars acts on the coefficient factor, transported across tensor symmetry. -/
noncomputable instance baseChangeModule : Module B' (M ⊗[B] B') :=
  (TensorProduct.comm B M B').toAddEquiv.module B'

/-- The coefficient-factor action extends the original `B`-action. -/
instance baseChangeModule_scalarTower : IsScalarTower B B' (M ⊗[B] B') :=
  (TensorProduct.comm B M B').isScalarTower (A := B')

/-- The scalar-tower action on each exterior-form term restricts scalars along `B → B'`. -/
instance moduleRestrictScalars_form (p : ℕ) : Module B (exteriorPower.form B' Ω' p) :=
  exteriorPower.form.moduleOfScalarTower (A := B) (B := B') (M := Ω') p

/-- The restricted action on exterior forms is compatible with their `B'`-module structure. -/
instance isScalarTower_formRestrictScalars (p : ℕ) :
    IsScalarTower B B' (exteriorPower.form B' Ω' p) :=
  exteriorPower.form.isScalarTower_moduleOfScalarTower (A := B) (B := B') (M := Ω') p

/-- The scalar action on extended coefficients induces a restricted action on form tensors. -/
noncomputable instance moduleRestrictScalars_baseChangeTensor (p : ℕ) :
    Module B ((M ⊗[B] B') ⊗[B'] exteriorPower.form B' Ω' p) :=
  TensorProduct.leftModule

/-- The coefficient inclusion sends `m` to `m ⊗ₜ[B] 1`. -/
def coeffInclude : M →ₗ[B] M ⊗[B] B' :=
  (TensorProduct.mk B M B').flip 1

/-- A linear map of one-forms induces the exterior-form map over the scalar extension. -/
noncomputable def inducedForm (φ : Ω →ₗ[B] Ω') :
    (p : ℕ) → exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B' Ω' p
  | 0 => Algebra.linearMap B B'
  | 1 => φ
  | degree + 2 =>
      let generator : Ω' [⋀^Fin (degree + 2)]→ₗ[B'] exteriorPower.form B' Ω' (degree + 2) :=
        exteriorPower.ιMulti B' (degree + 2)
      exteriorPower.alternatingMapLinearEquiv
        (({ generator.toMultilinearMap.restrictScalars B with
          map_eq_zero_of_eq' := fun entries first second heq hne ↦
            generator.map_eq_zero_of_eq entries (i := first) (j := second) heq hne } :
          Ω' [⋀^Fin (degree + 2)]→ₗ[B] exteriorPower.form B' Ω' (degree + 2)).compLinearMap φ)

/-- The coefficient-and-form map preserves the coefficient and applies the induced form map. -/
noncomputable def baseChangeForm (φ : Ω →ₗ[B] Ω') (p : ℕ) :
    M ⊗[B] exteriorPower.form B Ω p →ₗ[B] M ⊗[B] exteriorPower.form B' Ω' p :=
  TensorProduct.map (LinearMap.id : M →ₗ[B] M) (inducedForm φ p)

/-- Cancelling the extended coefficient ring identifies the two form tensor products. -/
noncomputable def cancelBaseChange_form (p : ℕ) :
    (M ⊗[B] B') ⊗[B'] exteriorPower.form B' Ω' p ≃ₗ[B]
      M ⊗[B] exteriorPower.form B' Ω' p :=
  ((TensorProduct.congr
      ((TensorProduct.comm B M B').toAddEquiv.linearEquiv B')
      (LinearEquiv.refl B' (exteriorPower.form B' Ω' p))).trans
    ((TensorProduct.comm B' (B' ⊗[B] M) (exteriorPower.form B' Ω' p)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'
        (exteriorPower.form B' Ω' p) M))).restrictScalars B |>.trans
    (TensorProduct.comm B (exteriorPower.form B' Ω' p) M)

/-- Extending coefficients in a form tensor is the inverse of tensor cancellation. -/
noncomputable def toBaseChangeForm (p : ℕ) :
    M ⊗[B] exteriorPower.form B' Ω' p →ₗ[B]
      (M ⊗[B] B') ⊗[B'] exteriorPower.form B' Ω' p :=
  (cancelBaseChange_form p).symm.toLinearMap

/-- Forgetting the extended coefficient factor is tensor cancellation. -/
noncomputable def fromBaseChangeForm (p : ℕ) :
    (M ⊗[B] B') ⊗[B'] exteriorPower.form B' Ω' p →ₗ[B]
      M ⊗[B] exteriorPower.form B' Ω' p :=
  (cancelBaseChange_form p).toLinearMap

/-- Tensor cancellation sends the included coefficient tensor to the original coefficient tensor. -/
theorem cancelBaseChange_form_tmul (p : ℕ) (m : M) (η : exteriorPower.form B' Ω' p) :
    cancelBaseChange_form p ((m ⊗ₜ[B] (1 : B')) ⊗ₜ[B'] η) = m ⊗ₜ[B] η := sorry

/-- The explicit degreewise components consist of coefficient inclusion and induced form maps. -/
noncomputable def baseChangeDeRhamHom_f
    {D : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
    {D' : Derivation A' B' Ω'} {δ' : DifferentialOperator.DeRham.Family A' B' Ω'}
    (conn : Connection D M) (C : ExteriorCalculus D δ) (hconn : IsIntegrable conn C)
    (conn' : Connection D' (M ⊗[B] B')) (C' : ExteriorCalculus D' δ')
    (hconn' : IsIntegrable conn' C') (φ : Ω →ₗ[B] Ω') :
    (degree : ℕ) → (deRhamComplex conn C hconn).X degree ⟶
      (deRhamComplex conn' C' hconn').X degree
  | 0 => AddCommGrpCat.ofHom coeffInclude.toAddMonoidHom
  | p + 1 => AddCommGrpCat.ofHom
      (((toBaseChangeForm (p + 1)).comp (baseChangeForm φ (p + 1))).toAddMonoidHom)

/-- On pure tensors the coefficient-and-form map applies the exterior-form map to the form. -/
theorem baseChangeForm_tmul (φ : Ω →ₗ[B] Ω') (p : ℕ) (m : M)
    (η : exteriorPower.form B Ω p) :
    (baseChangeForm φ p : M ⊗[B] exteriorPower.form B Ω p →ₗ[B]
      M ⊗[B] exteriorPower.form B' Ω' p) (m ⊗ₜ[B] η) =
      m ⊗ₜ[B] inducedForm φ p η := sorry

/-- Compatible exterior calculi preserve derivations, differentials, and both wedge operations. -/
structure CompatibleCalculi
    {D : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
    {D' : Derivation A' B' Ω'} {δ' : DifferentialOperator.DeRham.Family A' B' Ω'}
    (φ : Ω →ₗ[B] Ω') (C : ExteriorCalculus D δ) (C' : ExteriorCalculus D' δ') : Prop where
  /-- The one-form map intertwines the derivations. -/
  derivation (b : B) : φ (D b) = D' (algebraMap B B' b)
  /-- The induced form maps intertwine the differentials. -/
  differential (p : ℕ) (ω : exteriorPower.form B Ω p) :
    inducedForm φ (p + 1) (δ p ω) = δ' p (inducedForm φ p ω)
  /-- The induced form maps preserve left wedge by a one-form. -/
  wedge (p : ℕ) (η : Ω) (ω : exteriorPower.form B Ω p) :
    inducedForm φ (p + 1) (C.leftWedge p η ω) = C'.leftWedge p (φ η) (inducedForm φ p ω)
  /-- The induced form maps preserve left wedge by a two-form. -/
  wedgeTwo (p : ℕ) (η : exteriorPower.form B Ω 2) (ω : exteriorPower.form B Ω p) :
    inducedForm φ (p + 2) (C.leftWedgeTwo p η ω) =
      C'.leftWedgeTwo p (inducedForm φ 2 η) (inducedForm φ p ω)

variable {D : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
variable {D' : Derivation A' B' Ω'} {δ' : DifferentialOperator.DeRham.Family A' B' Ω'}

/-- Four intertwining equations construct compatibility of exterior calculi. -/
def CompatibleCalculi.of (φ : Ω →ₗ[B] Ω') (C : ExteriorCalculus D δ) (C' : ExteriorCalculus D' δ')
    (hderivation : ∀ b, φ (D b) = D' (algebraMap B B' b))
    (hdifferential : ∀ p ω, inducedForm φ (p + 1) (δ p ω) = δ' p (inducedForm φ p ω))
    (hwedge : ∀ p η ω, inducedForm φ (p + 1) (C.leftWedge p η ω) =
      C'.leftWedge p (φ η) (inducedForm φ p ω))
    (hwedgeTwo : ∀ p η ω, inducedForm φ (p + 2) (C.leftWedgeTwo p η ω) =
      C'.leftWedgeTwo p (inducedForm φ 2 η) (inducedForm φ p ω)) : CompatibleCalculi φ C C' :=
  ⟨hderivation, hdifferential, hwedge, hwedgeTwo⟩

/-- Compatibility is equivalent to preservation of the derivations, differentials, and wedges. -/
theorem CompatibleCalculi.iff (φ : Ω →ₗ[B] Ω') (C : ExteriorCalculus D δ)
    (C' : ExteriorCalculus D' δ') :
    CompatibleCalculi φ C C' ↔
      (∀ b, φ (D b) = D' (algebraMap B B' b)) ∧
      (∀ p ω, inducedForm φ (p + 1) (δ p ω) = δ' p (inducedForm φ p ω)) ∧
      (∀ p η ω, inducedForm φ (p + 1) (C.leftWedge p η ω) =
        C'.leftWedge p (φ η) (inducedForm φ p ω)) ∧
      (∀ p η ω, inducedForm φ (p + 2) (C.leftWedgeTwo p η ω) =
        C'.leftWedgeTwo p (inducedForm φ 2 η) (inducedForm φ p ω)) := sorry

/-- The scalar-extension connection value is the transported connection plus the scalar derivative. -/
noncomputable def scalarExtensionValue (D' : Derivation A' B' Ω') (conn : Connection D M)
    (φ : Ω →ₗ[B] Ω') (m : M) (scalar : B') : (M ⊗[B] B') ⊗[B'] Ω' :=
  scalar • toBaseChangeForm 1 (baseChangeForm φ 1 (conn.toAddMonoidHom m)) +
    (m ⊗ₜ[B] (1 : B')) ⊗ₜ[B'] D' scalar

/-- The scalar-extension value is additive in the coefficient module. -/
theorem scalarExtensionValue_add_left (D' : Derivation A' B' Ω') (conn : Connection D M)
    (φ : Ω →ₗ[B] Ω') (first second : M) (scalar : B') :
    scalarExtensionValue D' conn φ (first + second) scalar =
      scalarExtensionValue D' conn φ first scalar + scalarExtensionValue D' conn φ second scalar := sorry

/-- The scalar-extension value is additive in the extended scalar. -/
theorem scalarExtensionValue_add_right (D' : Derivation A' B' Ω') (conn : Connection D M)
    (φ : Ω →ₗ[B] Ω') (m : M) (first second : B') :
    scalarExtensionValue D' conn φ m (first + second) =
      scalarExtensionValue D' conn φ m first + scalarExtensionValue D' conn φ m second := sorry

/-- The scalar-extension values form an additive pairing in the coefficient and scalar. -/
noncomputable def scalarExtensionPairing (D' : Derivation A' B' Ω') (conn : Connection D M)
    (φ : Ω →ₗ[B] Ω') : M →+ B' →+ (M ⊗[B] B') ⊗[B'] Ω' :=
  AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk' (scalarExtensionValue D' conn φ m)
    (scalarExtensionValue_add_right D' conn φ m))
    (fun first second ↦ AddMonoidHom.ext (scalarExtensionValue_add_left D' conn φ first second))

/-- Intertwining derivations makes the scalar-extension pairing balanced over the original ring. -/
theorem scalarExtensionPairing_balanced (D' : Derivation A' B' Ω') (conn : Connection D M)
    (φ : Ω →ₗ[B] Ω') (hφD : ∀ b, φ (D b) = D' (algebraMap B B' b))
    (b : B) (m : M) (scalar : B') :
    scalarExtensionPairing D' conn φ (b • m) scalar =
      scalarExtensionPairing D' conn φ m (b • scalar) := sorry

/-- The balanced scalar-extension pairing lifts to an additive map on the tensor product. -/
noncomputable def scalarExtensionMap (conn : Connection D M) (φ : Ω →ₗ[B] Ω')
    (hφD : ∀ b, φ (D b) = D' (algebraMap B B' b)) :
    M ⊗[B] B' →+ (M ⊗[B] B') ⊗[B'] Ω' :=
  TensorProduct.liftAddHom (scalarExtensionPairing D' conn φ)
    (scalarExtensionPairing_balanced D' conn φ hφD)

/-- The scalar-extension map satisfies the connection Leibniz rule over the extended ring. -/
theorem scalarExtensionMap_leibniz (conn : Connection D M) (φ : Ω →ₗ[B] Ω')
    (hφD : ∀ b, φ (D b) = D' (algebraMap B B' b)) (scalar : B') (tensor : M ⊗[B] B') :
    scalarExtensionMap conn φ hφD (scalar • tensor) =
      scalar • scalarExtensionMap conn φ hφD tensor + tensor ⊗ₜ[B'] D' scalar := sorry

/-- The scalar extension of a connection is obtained by the tensor Leibniz formula. -/
noncomputable def scalarExtension (conn : Connection D M) (φ : Ω →ₗ[B] Ω')
    (hφD : ∀ b, φ (D b) = D' (algebraMap B B' b)) : Connection D' (M ⊗[B] B') :=
  Connection.of (scalarExtensionMap conn φ hφD) (scalarExtensionMap_leibniz conn φ hφD)

/-- On pure tensors the scalar-extension connection has its specified Leibniz value. -/
theorem scalarExtension_apply_tmul (conn : Connection D M) (φ : Ω →ₗ[B] Ω')
    (hφD : ∀ b, φ (D b) = D' (algebraMap B B' b)) (m : M) (scalar : B') :
    (scalarExtension conn φ hφD).toAddMonoidHom (m ⊗ₜ[B] scalar) =
      scalarExtensionValue D' conn φ m scalar := sorry

/-- The explicit base-change components commute with the de Rham differentials. -/
theorem baseChangeDeRhamHom_comm (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (C' : ExteriorCalculus D' δ') (φ : Ω →ₗ[B] Ω')
    (compat : CompatibleCalculi φ C C')
    (hconn' : IsIntegrable (scalarExtension conn φ compat.derivation) C') (first second : ℕ) :
    baseChangeDeRhamHom_f conn C hconn (scalarExtension conn φ compat.derivation) C' hconn' φ first ≫
        (deRhamComplex (scalarExtension conn φ compat.derivation) C' hconn').d first second =
      (deRhamComplex conn C hconn).d first second ≫
        baseChangeDeRhamHom_f conn C hconn (scalarExtension conn φ compat.derivation) C' hconn' φ second := sorry

end Connection
