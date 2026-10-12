/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import ReasLib.Algebra.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/-- The canonical map from a base-changed finite model `B ⊗[R] C'` to its open
subalgebra `C`. -/
def Algebra.RelativeDual.baseChangeHom
    (R B C' C : Type u)
    [CommRing R] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra R B] [Algebra R C'] [Algebra R C] [Algebra B C] [Algebra C' C]
    [IsScalarTower R B C] [IsScalarTower R C' C] :
    (B ⊗[R] C') →ₐ[B] C :=
  Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom R C' C) (fun _ _ ↦ mul_comm _ _)

/-- The canonical algebra structure on `C` over the base-changed finite model
`B ⊗[R] C'`. -/
scoped instance Algebra.RelativeDual.baseChangeAlgebra
    (R B C' C : Type u)
    [CommRing R] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra R B] [Algebra R C'] [Algebra R C] [Algebra B C] [Algebra C' C]
    [IsScalarTower R B C] [IsScalarTower R C' C] :
    Algebra (B ⊗[R] C') C :=
  (Algebra.RelativeDual.baseChangeHom R B C' C).toAlgebra

open scoped Algebra.RelativeDual

/-- The canonical base-change algebra structure is compatible with the map
`B → C`. -/
scoped instance Algebra.RelativeDual.baseChangeIsScalarTower
    (R B C' C : Type u)
    [CommRing R] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra R B] [Algebra R C'] [Algebra R C] [Algebra B C] [Algebra C' C]
    [IsScalarTower R B C] [IsScalarTower R C' C] :
    IsScalarTower B (B ⊗[R] C') C := sorry

/-- Base change of the finite open model `C' → C` along `R → B` is again
an open model of `C`. -/
theorem Algebra.RelativeDual.baseChange_isOpenImmersion
    (R B C' C : Type u)
    [CommRing R] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra R B] [Algebra R C'] [Algebra R C] [Algebra B C] [Algebra C' C]
    [IsScalarTower R B C] [IsScalarTower R C' C]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (B ⊗[R] C') C))) := sorry

/-- The scalar action of an extension ring on its relative dual commutes with the
scalar action of the base ring. -/
instance Algebra.RelativeDual.instSMulCommClass
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    SMulCommClass A B (Module.Dual A B) := sorry

/-- A chosen relative dualizing module over `T` carries the compatible action of
the base ring `R` through its right tensor factor. -/
scoped instance Algebra.RelativeDual.relativeDualizingBaseModule
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite R T) [Module.Finite R S]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T)))) :
    Module R (Algebra.RelativeDualizingModule.of R S T h_quasiFinite h_open) :=
  TensorProduct.Right.module

/-- The base-ring and extension-ring actions on a chosen relative dualizing
module commute. -/
scoped instance Algebra.RelativeDual.relativeDualizingSMulCommClass
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite R T) [Module.Finite R S]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T)))) :
    SMulCommClass R T
      (Algebra.RelativeDualizingModule.of R S T h_quasiFinite h_open) := sorry

namespace Algebra.RelativeDualizingModule

/-- The base-change map between relative dualizing modules for chosen finite
factorizations, when both the ambient algebra and its finite model are related by
base change. -/
noncomputable def baseChangeOf
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap) :
    RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₛₗ[algebraMap B B₁]
      RelativeDualizingModule.of A₁ B₁' B₁ h_quasiFinite₁ h_open₁ where
  toFun := TensorProduct.liftAddHom
    ({ toFun := fun f ↦
        { toFun := fun b ↦
            h_finiteModel.toDual f ⊗ₜ[B₁'] algebraMap B B₁ b
          map_zero' := sorry
          map_add' := sorry }
       map_zero' := sorry
       map_add' := sorry } :
      Module.Dual A B' →+
        (B →+ (Module.Dual A₁ B₁' ⊗[B₁'] B₁)))
    sorry
  map_add' := sorry
  map_smul' := sorry

/-- On a pure tensor, `baseChangeOf` applies finite-dual base change to the first
factor and the ring base-change map to the second factor. -/
theorem baseChangeOf_tmul
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap)
    (f : Module.Dual A B') (b : B) :
    baseChangeOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel (f ⊗ₜ[B'] b) =
      h_finiteModel.toDual f ⊗ₜ[B₁'] algebraMap B B₁ b := sorry

end Algebra.RelativeDualizingModule
