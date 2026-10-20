/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Square-zero comparisons for naive cotangent objects

A Λ-algebra map π : A' → A induces a derived cotangent comparison and a
comparison of Kähler differentials after residue base change. A square-zero
surjection also gives its conormal module a canonical A-module structure.
-/

@[expose] public section

open CategoryTheory
open Algebra.Generators
open HomologicalComplex
open ComplexShape
open scoped NaiveCotangent TensorProduct

universe u

noncomputable section

namespace Algebra.NaiveCotangent

variable {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
variable [Algebra Λ A'] [Algebra Λ A]

/-- The conormal module of `ker π`, i.e. `ker π / (ker π)²`. -/
abbrev squareZeroKernel (π : A' →ₐ[Λ] A) : Type u :=
  Ideal.Cotangent (RingHom.ker π.toRingHom)

/-- The conormal module of a square-zero surjection, with the target-ring action
transported along the quotient-kernel equivalence. -/
def squareZeroKernelModule (π : A' →ₐ[Λ] A)
    (hπ : π.toRingHom.IsSquareZeroExtension) : ModuleCat.{u} A :=
  @ModuleCat.of A _ (squareZeroKernel π) inferInstance
    (Module.compHom (squareZeroKernel π)
      (RingHom.quotientKerEquivOfSurjective hπ.surjective).symm.toRingHom)

/-- Derived comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` induced by the self-presentations
along a tower `Λ → A' → A`. -/
def naiveCotangentMapOfTower [Algebra A' A] [IsScalarTower Λ A' A] :
    Algebra.naiveCotangentObject Λ A ⟶ Algebra.naiveCotangentObject A' A :=
  DerivedCategory.Q.map
    (extendMap
      (Extension.NaiveCotangent.chainMap
        (defaultHom (self Λ A) (self A' A)).toExtensionHom)
      embeddingDownNat)

/-- Derived comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` along a Λ-algebra map `π`. -/
def naiveCotangentMap (π : A' →ₐ[Λ] A) :
    Algebra.naiveCotangentObject Λ A ⟶
      @Algebra.naiveCotangentObject A' A _ _ π.toRingHom.toAlgebra :=
  @naiveCotangentMapOfTower Λ A' A _ _ _ _ _ π.toRingHom.toAlgebra
    (IsScalarTower.of_algHom π)

variable {k : Type u} [Field k] [Algebra A k]

/-- Canonical comparison `k ⊗[A'] Ω[A'⁄Λ] →ₗ[k] k ⊗[A] Ω[A⁄Λ]` for a tower
`Λ → A' → A → k`. -/
def kaehlerMapTensorResidue [Algebra A' A] [IsScalarTower Λ A' A]
    [Algebra A' k] [IsScalarTower A' A k] :
    k ⊗[A'] Ω[A'⁄Λ] →ₗ[k] k ⊗[A] Ω[A⁄Λ] :=
  (KaehlerDifferential.mapBaseChange Λ A' A).baseChange k ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
        A' A k k Ω[A'⁄Λ]).symm.toLinearMap

/-- Evaluation of `kaehlerMapTensorResidue` on elementary tensors. -/
theorem kaehlerMapTensorResidue_apply [Algebra A' A] [IsScalarTower Λ A' A]
    [Algebra A' k] [IsScalarTower A' A k] (x : k) (ω : Ω[A'⁄Λ]) :
    kaehlerMapTensorResidue (x ⊗ₜ ω) =
      (KaehlerDifferential.mapBaseChange Λ A' A).baseChange k
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange
            A' A k k Ω[A'⁄Λ]).symm (x ⊗ₜ ω)) :=
  sorry

/-- The `A'`-algebra structure on `k` obtained by composing `π` with `A → k`. -/
abbrev residueAlgebra (π : A' →ₐ[Λ] A) : Algebra A' k :=
  RingHom.toAlgebra ((algebraMap A k).comp π.toRingHom)

/-- The scalar tower `A' → A → k` determined by `π`. -/
abbrev residueTower (π : A' →ₐ[Λ] A) :
    @IsScalarTower A' A k π.toRingHom.toAlgebra.toSMul Algebra.toSMul
      (residueAlgebra π).toSMul :=
  @IsScalarTower.of_algebraMap_eq' A' A k _ _ _ π.toRingHom.toAlgebra inferInstance
    (residueAlgebra π) rfl

/-- Kaehler comparison along `π`, using the algebra structures determined by `π`. -/
def kaehlerMapAlong (π : A' →ₐ[Λ] A) :=
  @kaehlerMapTensorResidue Λ A' A _ _ _ _ _ k _ _ π.toRingHom.toAlgebra
    (IsScalarTower.of_algHom π) (residueAlgebra π) (residueTower π)

end Algebra.NaiveCotangent
