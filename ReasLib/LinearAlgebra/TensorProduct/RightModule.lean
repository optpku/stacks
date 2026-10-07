module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.ScopedNS

/-!
# Right Tensor-Product Module Structures

Mathlib canonically equips `M ⊗[R] N` with scalar actions carried by the
left factor.  This file provides the complementary, non-global choice: when
the right factor `N` is an `S`-module, `open scoped TensorProduct.Right`
selects the transported `S`-module structure on `M ⊗[R] N`.

The scope also makes available the associated scalar-tower, commutation, and
`A ⊗[R] S`-module structures.  None is globally registered, since the two
tensor factors can give genuinely distinct actions on a self-tensor product.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.Right

universe u v w x

section Module

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Module S N]
variable [SMulCommClass R S N]

/-- The `S`-module structure on `M ⊗[R] N` induced by the right factor. -/
abbrev module : Module S (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module S

/-- The right-factor action scales the right component of a pure tensor. -/
theorem smul_tmul (s : S) (m : M) (n : N) :
    -- Local instance justification (noncanonical choice): the right-factor action competes with the canonical left-factor action.
    letI : Module S (M ⊗[R] N) := module
    s • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (s • n) := sorry

end Module

section Tower

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Module S N]
variable [SMulCommClass R S N] [SMul R S] [IsScalarTower R S N]

/-- The right-factor action on `M ⊗[R] N` is compatible with the base ring. -/
theorem isScalarTower :
    -- Local instance justification (noncanonical choice): the right-factor action competes with the canonical left-factor action.
    letI : Module S (M ⊗[R] N) := module
    IsScalarTower R S (M ⊗[R] N) := sorry

end Tower

section TensorAlgebra

variable {R : Type u} {A : Type v} {S : Type w} {M : Type x} {N : Type*}
variable [CommSemiring R] [Semiring A] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Module A M] [Module S N]
variable [Algebra R A] [Algebra R S]
variable [IsScalarTower R A M] [IsScalarTower R S N]
variable [SMulCommClass R A M] [SMulCommClass R S N]

/-- The left `A`- and right `S`-actions on `M ⊗[R] N` commute. -/
theorem smulCommClass :
    -- Local instance justification (noncanonical choice): the right-factor action competes with the canonical left-factor action.
    letI : Module S (M ⊗[R] N) := module
    SMulCommClass A S (M ⊗[R] N) := sorry

/-- The action of `A ⊗[R] S` on `M ⊗[R] N` induced by its two tensor factors. -/
abbrev algebraModule : Module (A ⊗[R] S) (M ⊗[R] N) := by
  -- Local instance justification (noncanonical choice): this pins the left-factor action while combining it with the competing right-factor action.
  letI : Module A (M ⊗[R] N) := TensorProduct.leftModule
  -- Local instance justification (noncanonical choice): this pins the tower for the selected left-factor action before combining both actions.
  letI : IsScalarTower R A (M ⊗[R] N) := TensorProduct.isScalarTower_left
  -- Local instance justification (noncanonical choice): the right-factor action competes with the selected left-factor action.
  letI : Module S (M ⊗[R] N) := module
  -- Local instance justification (noncanonical choice): this tower belongs to the selected competing right-factor action.
  letI : IsScalarTower R S (M ⊗[R] N) := isScalarTower
  -- Local instance justification (noncanonical choice): this commutation law combines the selected left- and right-factor actions.
  letI : SMulCommClass A S (M ⊗[R] N) := smulCommClass
  exact TensorProduct.Algebra.module

/-- A pure scalar acts by its two tensor-factor actions. -/
theorem algebraModule_tmul_smul (a : A) (s : S) (m : M) (n : N) :
    -- Local instance justification (noncanonical choice): the tensor-algebra action incorporates the competing right-factor action.
    letI : Module (A ⊗[R] S) (M ⊗[R] N) := algebraModule
    (a ⊗ₜ[R] s : A ⊗[R] S) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (s • n) := sorry

/-- The `A ⊗[R] S`-action on `M ⊗[R] N` extends its base `R`-module structure. -/
theorem algebraIsScalarTower :
    -- Local instance justification (noncanonical choice): the tensor-algebra action incorporates the competing right-factor action.
    letI : Module (A ⊗[R] S) (M ⊗[R] N) := algebraModule
    IsScalarTower R (A ⊗[R] S) (M ⊗[R] N) := sorry

/-- The tensor-product action also extends the canonical left-factor `A`-action.  This is the
bridge used when an `A ⊗[R] S`-submodule is regarded as an `A`-submodule via the left inclusion. -/
theorem algebraIsScalarTowerLeft :
    -- Local instance justification (noncanonical choice): the tensor-algebra action incorporates the competing right-factor action.
    letI : Module (A ⊗[R] S) (M ⊗[R] N) := algebraModule
    IsScalarTower A (A ⊗[R] S) (M ⊗[R] N) := sorry

/-- The tensor-product algebra action commutes with the ambient `R`-action. -/
theorem algebraSmulCommClass :
    -- Local instance justification (noncanonical choice): the tensor-algebra action incorporates the competing right-factor action.
    letI : Module (A ⊗[R] S) (M ⊗[R] N) := algebraModule
    SMulCommClass (A ⊗[R] S) R (M ⊗[R] N) := sorry

end TensorAlgebra

end TensorProduct.Right

/-! The scope chooses the right-oriented actions only when requested by a consumer.
The lower priority preserves Mathlib's canonical left-factor action when both
descriptions apply, in particular when the added scalar ring is the base ring. -/
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.module
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.isScalarTower
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.algebraModule
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.algebraIsScalarTower
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.algebraIsScalarTowerLeft
scoped[TensorProduct.Right] attribute [instance 100] TensorProduct.Right.algebraSmulCommClass
