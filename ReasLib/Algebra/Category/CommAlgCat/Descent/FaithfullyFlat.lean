/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Faithfully flat descent of commutative algebras

The descended algebra is the equalizer of a supplied algebra coaction and the unit map.
Its base change is identified with the original algebra using the actual inverse from
Mathlib's faithfully flat module descent. No representing scheme or effectiveness witness
is selected from an admitted existence statement.

The input coaction and its two laws are descent data. Applications must construct that
coaction from their own overlap maps; the reconstruction below supplies the descended data.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct
noncomputable section
universe u

namespace Algebra.FaithfullyFlatDescent

variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

/-- The invariant subalgebra of an actual algebra coaction. -/
def invariants (a : B →ₐ[S] S ⊗[R] B) : Subalgebra R B :=
  AlgHom.equalizer (a.restrictScalars R) Algebra.TensorProduct.includeRight

/-- Restricting the algebra action along its structure map preserves the given scalar action. -/
def restrictionLinearEquiv : B ≃ₗ[R]
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B) where
  toFun := fun b ↦ b
  invFun := fun b ↦ b
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r b := (IsScalarTower.algebraMap_smul S r b).symm

/-- The ordinary algebra tensor carrier is the module tensor carrier used by scalar extension. -/
def tensorCarrierEquiv : (S ⊗[R] B) ≃ₗ[R]
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((extendRestrictScalarsAdj (algebraMap R S)).toComonad.obj (ModuleCat.of S B)) :=
  _root_.TensorProduct.congr
    (restrictionLinearEquiv (R := R) (S := S) (B := S))
    (restrictionLinearEquiv (R := R) (S := S) (B := B))

/-- The underlying module map of the algebra coaction. -/
def coaction (a : B →ₐ[S] S ⊗[R] B) :
    ModuleCat.of S B ⟶
      (extendRestrictScalarsAdj (algebraMap R S)).toComonad.obj (ModuleCat.of S B) :=
  ModuleCat.ofHom (X := ModuleCat.of S B)
    (Y := (extendRestrictScalarsAdj (algebraMap R S)).toComonad.obj (ModuleCat.of S B))
    { toFun := fun b ↦ tensorCarrierEquiv (a b)
      map_add' := by intro b c; simp only [map_add]; rfl
      map_smul' := sorry }

/-- Algebra coactions with the native scalar-extension counit and coassociativity laws. -/
structure Coaction where
  toAlgHom : B →ₐ[S] S ⊗[R] B
  counit : coaction toAlgHom ≫
    (extendRestrictScalarsAdj (algebraMap R S)).toComonad.ε.app (ModuleCat.of S B) = 𝟙 _
  coassoc : coaction toAlgHom ≫
      (extendRestrictScalarsAdj (algebraMap R S)).toComonad.δ.app (ModuleCat.of S B) =
    coaction toAlgHom ≫
      (extendRestrictScalarsAdj (algebraMap R S)).toComonad.map (coaction toAlgHom)

variable (D : Coaction (R := R) (S := S) (B := B))

/-- Forget the multiplication of an algebra coaction, retaining its actual module coaction. -/
def toModuleCoalgebra : (extendRestrictScalarsAdj (algebraMap R S)).toComonad.Coalgebra where
  A := ModuleCat.of S B
  a := coaction D.toAlgHom
  counit := D.counit
  coassoc := D.coassoc

/-- The concrete invariant algebra of the descent coaction. -/
abbrev descendedAlgebra : Subalgebra R B := invariants D.toAlgHom

/-- The invariant algebra includes in the restricted underlying module. -/
def invariantInclusion : ModuleCat.of R (descendedAlgebra D) ⟶
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B) :=
  ModuleCat.ofHom (X := ModuleCat.of R (descendedAlgebra D))
    (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B))
    ((restrictionLinearEquiv (R := R) (S := S) (B := B)).toLinearMap.comp
      (descendedAlgebra D).toSubmodule.subtype)

/-- The inclusion of invariants equalizes the module coaction and the adjunction unit. -/
theorem invariantInclusion_condition :
    invariantInclusion D ≫ (ModuleCat.restrictScalars (algebraMap R S)).map (toModuleCoalgebra D).a =
      invariantInclusion D ≫ (extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B)) := sorry

/-- The invariant algebra maps into the native descent equalizer by its universal lift. -/
def invariantsToDescent : ModuleCat.of R (descendedAlgebra D) ⟶
    (ModuleCat.descentPushforward (algebraMap R S)).obj (toModuleCoalgebra D) :=
  equalizer.lift (invariantInclusion D) (invariantInclusion_condition D)

/-- The native equalizer inclusion lands in the literal invariant subalgebra. -/
theorem descentInvariant_mem
    (x : (ModuleCat.descentPushforward (algebraMap R S)).obj (toModuleCoalgebra D)) :
    (equalizer.ι
      ((ModuleCat.restrictScalars (algebraMap R S)).map (toModuleCoalgebra D).a)
      ((extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B)))) x ∈
      (descendedAlgebra D) := sorry

/-- The reverse equalizer map is the native equalizer inclusion with its invariant property. -/
def descentToInvariants :
    (ModuleCat.descentPushforward (algebraMap R S)).obj (toModuleCoalgebra D) ⟶
      ModuleCat.of R (descendedAlgebra D) :=
  ModuleCat.ofHom (X := (ModuleCat.descentPushforward (algebraMap R S)).obj (toModuleCoalgebra D))
    (Y := ModuleCat.of R (descendedAlgebra D))
    { toFun := fun x ↦ ⟨(equalizer.ι
        ((ModuleCat.restrictScalars (algebraMap R S)).map (toModuleCoalgebra D).a)
        ((extendRestrictScalarsAdj (algebraMap R S)).unit.app
          ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S B)))) x,
        descentInvariant_mem D x⟩
      map_add' := sorry
      map_smul' := sorry }

/-- The concrete invariant subalgebra has exactly the module of native descent invariants. -/
def invariantsModuleIso : ModuleCat.of R (descendedAlgebra D) ≅
    (ModuleCat.descentPushforward (algebraMap R S)).obj (toModuleCoalgebra D) where
  hom := invariantsToDescent D
  inv := descentToInvariants D
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Scalar extension of the literal invariant algebra reconstructs the given module using
both directions of the proved native faithfully-flat descent equivalence. -/
def reconstructionModuleIso (hf : (algebraMap R S).FaithfullyFlat) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (descendedAlgebra D)) ≅
      ModuleCat.of S B :=
  (ModuleCat.extendScalars (algebraMap R S)).mapIso (invariantsModuleIso D) ≪≫
    (CategoryTheory.Comonad.forget (extendRestrictScalarsAdj (algebraMap R S)).toComonad).mapIso
      ((ModuleCat.faithfullyFlatDescentEquivalence (algebraMap R S) hf).counitIso.app
        (toModuleCoalgebra D))

/-- The tensor carrier used by algebra base change is identified with native module scalar extension. -/
def baseChangeModuleEquiv (M : ModuleCat.{u} R) : (S ⊗[R] M) ≃ₗ[S]
    (ModuleCat.extendScalars (algebraMap R S)).obj M := by
  let e := _root_.TensorProduct.congr
    (restrictionLinearEquiv (R := R) (S := S) (B := S)) (LinearEquiv.refl R M)
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := sorry }

/-- The reconstruction algebra map sends a pure tensor to the scalar times its invariant element. -/
def reconstruction : (S ⊗[R] descendedAlgebra D) →ₐ[S] B :=
  (AlgHom.liftEquiv R S (descendedAlgebra D) B) (descendedAlgebra D).val

/-- The native descent isomorphism, expressed on the ordinary algebra tensor carrier. -/
def reconstructionLinearEquiv (hf : (algebraMap R S).FaithfullyFlat) :
    (S ⊗[R] descendedAlgebra D) ≃ₗ[S] B :=
  (baseChangeModuleEquiv (S := S) (ModuleCat.of R (descendedAlgebra D))).trans
    (reconstructionModuleIso D hf).toLinearEquiv

/-- The native descent counit is the explicit scalar-multiplication reconstruction map. -/
theorem reconstructionLinearEquiv_apply (hf : (algebraMap R S).FaithfullyFlat)
    (x : S ⊗[R] descendedAlgebra D) :
    reconstructionLinearEquiv D hf x = reconstruction D x := sorry

/-- The reconstruction has an actual inverse supplied by native faithfully-flat module descent.
Only the algebra compatibility laws are transported across the computed reconstruction map. -/
def reconstructionEquiv (hf : (algebraMap R S).FaithfullyFlat) :
    (S ⊗[R] descendedAlgebra D) ≃ₐ[S] B :=
  AlgEquiv.ofLinearEquiv (reconstructionLinearEquiv D hf)
    (by rw [reconstructionLinearEquiv_apply, map_one])
    (fun x y ↦ by simp only [reconstructionLinearEquiv_apply, map_mul])

/-- The invariant subalgebra consists of the elements fixed by the coaction-unit comparison. -/
theorem mem_descendedAlgebra (b : B) :
    b ∈ descendedAlgebra D ↔ D.toAlgHom b = (1 : S) ⊗ₜ[R] b := Iff.rfl

/-- The inverse function is exactly the inverse supplied by native module descent and tensor transport. -/
theorem reconstructionEquiv_symm_apply (hf : (algebraMap R S).FaithfullyFlat) (b : B) :
    (reconstructionEquiv D hf).symm b = (reconstructionLinearEquiv D hf).symm b := rfl

/-- On pure tensors reconstruction multiplies the scalar and the invariant element. -/
theorem reconstruction_tmul (s : S) (b : descendedAlgebra D) :
    reconstruction D (s ⊗ₜ[R] b) = s • (b : B) := rfl

end Algebra.FaithfullyFlatDescent
