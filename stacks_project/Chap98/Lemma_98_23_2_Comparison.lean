/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Square-zero comparisons for naive cotangent objects

Along a Λ-algebra map π : A' → A, this leaf owns the kernel cotangent as an
A-module, the derived comparison NL{A⁄Λ} ⟶ NL{A⁄A'}, and the Kaehler
comparison k ⊗[A'] Ω[A'⁄Λ] → k ⊗[A] Ω[A⁄Λ].
-/

@[expose] public section

open CategoryTheory
open Algebra
open Generators
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

/-- `squareZeroKernel π` is the cotangent module of `ker π`. -/
theorem squareZeroKernel_eq (π : A' →ₐ[Λ] A) :
    squareZeroKernel π = Ideal.Cotangent (RingHom.ker π.toRingHom) :=
  sorry

/-- The `A`-module structure on `squareZeroKernel π` obtained by transporting
the canonical `(A' ⧸ ker π)`-action along the first isomorphism theorem. -/
instance instModule_squareZeroKernel (π : A' →ₐ[Λ] A)
    [hπ : π.toRingHom.IsSquareZeroExtension] :
    Module A (squareZeroKernel π) :=
  Module.compHom (squareZeroKernel π)
    (RingHom.quotientKerEquivOfSurjective hπ.surjective).symm.toRingHom

/-- Derived comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` induced by the self-presentations
along a tower `Λ → A' → A`. -/
def naiveCotangentMapOfTower [Algebra A' A] [IsScalarTower Λ A' A] :
    Algebra.naiveCotangentObject Λ A ⟶ Algebra.naiveCotangentObject A' A :=
  DerivedCategory.Q.map
    (extendMap
      (Extension.NaiveCotangent.chainMap
        (defaultHom (self Λ A) (self A' A)).toExtensionHom)
      embeddingDownNat)

/-- `naiveCotangentMapOfTower` is the derived image of the extended default
presentation chain map. -/
theorem naiveCotangentMapOfTower_eq [Algebra A' A] [IsScalarTower Λ A' A] :
    naiveCotangentMapOfTower =
      DerivedCategory.Q.map
        (extendMap
          (Extension.NaiveCotangent.chainMap
            (defaultHom (self Λ A) (self A' A)).toExtensionHom)
          embeddingDownNat) :=
  sorry

/-- Derived comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` along a Λ-algebra map `π`. -/
def naiveCotangentMap (π : A' →ₐ[Λ] A) :
    Algebra.naiveCotangentObject Λ A ⟶
      @Algebra.naiveCotangentObject A' A _ _ π.toRingHom.toAlgebra :=
  @naiveCotangentMapOfTower Λ A' A _ _ _ _ _ π.toRingHom.toAlgebra
    (IsScalarTower.of_algHom π)

/-- `naiveCotangentMap π` is `naiveCotangentMapOfTower` for the algebra structure
determined by `π`. -/
theorem naiveCotangentMap_eq (π : A' →ₐ[Λ] A) :
    naiveCotangentMap π =
      @naiveCotangentMapOfTower Λ A' A _ _ _ _ _ π.toRingHom.toAlgebra
        (IsScalarTower.of_algHom π) :=
  sorry

variable {k : Type u} [Field k] [Algebra A k]

/-- Canonical comparison `k ⊗[A'] Ω[A'⁄Λ] →ₗ[k] k ⊗[A] Ω[A⁄Λ]` for a tower
`Λ → A' → A → k`. -/
def kaehlerMapTensorResidue [Algebra A' A] [IsScalarTower Λ A' A]
    [Algebra A' k] [IsScalarTower A' A k] :
    k ⊗[A'] Ω[A'⁄Λ] →ₗ[k] k ⊗[A] Ω[A⁄Λ] :=
  (KaehlerDifferential.mapBaseChange Λ A' A).baseChange k ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
        A' A k k Ω[A'⁄Λ]).symm.toLinearMap

/-- `kaehlerMapTensorResidue` is base change of `mapBaseChange` after
cancelling the intermediate extension of scalars along `A' → A`. -/
theorem kaehlerMapTensorResidue_eq [Algebra A' A] [IsScalarTower Λ A' A]
    [Algebra A' k] [IsScalarTower A' A k] :
    kaehlerMapTensorResidue =
      (KaehlerDifferential.mapBaseChange Λ A' A).baseChange k ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
            A' A k k Ω[A'⁄Λ]).symm.toLinearMap :=
  sorry

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

/-- `residueAlgebra π` is the algebra structure of the composite `A' → A → k`. -/
theorem residueAlgebra_eq (π : A' →ₐ[Λ] A) :
    residueAlgebra π =
      RingHom.toAlgebra ((algebraMap A k).comp π.toRingHom) :=
  sorry

/-- The scalar tower `A' → A → k` determined by `π`. -/
abbrev residueTower (π : A' →ₐ[Λ] A) :
    @IsScalarTower A' A k π.toRingHom.toAlgebra.toSMul Algebra.toSMul
      (residueAlgebra π).toSMul :=
  @IsScalarTower.of_algebraMap_eq' A' A k _ _ _ π.toRingHom.toAlgebra inferInstance
    (residueAlgebra π) rfl

/-- `residueTower π` is the tower instance for the algebras determined by `π`. -/
theorem residueTower_eq (π : A' →ₐ[Λ] A) :
    residueTower π =
      @IsScalarTower.of_algebraMap_eq' A' A k _ _ _ π.toRingHom.toAlgebra inferInstance
        (residueAlgebra π) rfl :=
  sorry

/-- Kaehler comparison along `π`, using the algebra structures determined by `π`. -/
def kaehlerMapAlong (π : A' →ₐ[Λ] A) :=
  @kaehlerMapTensorResidue Λ A' A _ _ _ _ _ k _ _ π.toRingHom.toAlgebra
    (IsScalarTower.of_algHom π) (residueAlgebra π) (residueTower π)

/-- `kaehlerMapAlong π` is `kaehlerMapTensorResidue` for the algebra structures
determined by `π`. -/
theorem kaehlerMapAlong_eq (π : A' →ₐ[Λ] A) :
    kaehlerMapAlong π =
      @kaehlerMapTensorResidue Λ A' A _ _ _ _ _ k _ _ π.toRingHom.toAlgebra
        (IsScalarTower.of_algHom π) (residueAlgebra π) (residueTower π) :=
  sorry

/-- Predicate recording an `A`-linear equivalence between `squareZeroKernel π` and
`k`. -/
def IsKernelEquivResidue (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] (k : Type u) [Field k] [Algebra A k] : Prop :=
  Nonempty (squareZeroKernel π ≃ₗ[A] k)

/-- `IsKernelEquivResidue` is an `A`-linear equivalence of the square-zero kernel
with `k`. -/
theorem isKernelEquivResidue_iff (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] (k : Type u) [Field k] [Algebra A k] :
    IsKernelEquivResidue π k ↔ Nonempty (squareZeroKernel π ≃ₗ[A] k) :=
  sorry

end Algebra.NaiveCotangent
