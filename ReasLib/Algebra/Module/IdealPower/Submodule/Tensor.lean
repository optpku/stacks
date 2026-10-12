/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor multiplication into ideal-power submodules

This leaf owns the canonical multiplication map

`(I ^ n A) ⊗[A] M ⟶ I ^ n M`

and its functoriality in `M` and in the filtration exponent.  The construction is
independent of derived categories and can therefore be reused by ordinary module,
complex, and derived comparison APIs.
@stack 0G3N
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace Ideal.PowerSubmodule

section Linear

variable {A : Type u} [CommSemiring A]
variable (I : Ideal A) (n : ℕ)
variable (M : Type v) [AddCommMonoid M] [Module A M]

/-- Multiplication by an element of the regular-module adic stage lands in the
corresponding adic stage of every module. -/
@[stacks 0G3N "ideal-power scalar multiplication membership"]
theorem smul_mem (a : stage I A n) (m : M) :
    (a : A) • m ∈ stage I M n := sorry

/-- The value of ideal-power tensor multiplication on a pair of elements. -/
@[stacks 0G3N "ideal-power tensor multiplication value"]
def tensorValue (a : stage I A n) (m : M) : stage I M n :=
  ⟨(a : A) • m, smul_mem I n M a m⟩

/-- Ideal-power tensor multiplication is additive in its stage argument. -/
theorem tensorValue_add_left (a b : stage I A n) (m : M) :
    tensorValue I n M (a + b) m = tensorValue I n M a m + tensorValue I n M b m := sorry

/-- Ideal-power tensor multiplication is linear in its stage argument. -/
theorem tensorValue_smul_left (r : A) (a : stage I A n) (m : M) :
    tensorValue I n M (r • a) m = r • tensorValue I n M a m := sorry

/-- Ideal-power tensor multiplication is additive in its module argument. -/
theorem tensorValue_add_right (a : stage I A n) (m₁ m₂ : M) :
    tensorValue I n M a (m₁ + m₂) =
      tensorValue I n M a m₁ + tensorValue I n M a m₂ := sorry

/-- Ideal-power tensor multiplication is linear in its module argument. -/
theorem tensorValue_smul_right (r : A) (a : stage I A n) (m : M) :
    tensorValue I n M a (r • m) = r • tensorValue I n M a m := sorry

/-- The curried bilinear multiplication map from a regular-module adic stage. -/
@[stacks 0G3N "ideal-power bilinear multiplication"]
def tensorBilinear : stage I A n →ₗ[A] M →ₗ[A] stage I M n :=
  LinearMap.mk₂ A (tensorValue I n M)
    (tensorValue_add_left I n M) (tensorValue_smul_left I n M)
    (tensorValue_add_right I n M) (tensorValue_smul_right I n M)

/-- The linear multiplication map `(I ^ n A) ⊗[A] M →ₗ[A] I ^ n M`. -/
@[stacks 0G3N "ideal-power tensor multiplication"]
def tensorLinearMap :
    TensorProduct A (stage I A n) M →ₗ[A] stage I M n :=
  TensorProduct.lift (tensorBilinear I n M)

/-- Forgetting the target submodule identifies tensor multiplication with the ambient
scalar-action map. -/
@[stacks 0G3N "ambient formula for unbundled ideal-power tensor multiplication"]
theorem tensorLinearMap_comp_subtype :
    (subtype I M n).comp (tensorLinearMap I n M) =
      TensorProduct.lift ((LinearMap.lsmul A M).comp (subtype I A n)) := sorry

/-- The unbundled ideal-power tensor multiplication is natural in the module. -/
@[stacks 0G3N "naturality of unbundled ideal-power tensor multiplication"]
theorem tensorLinearMap_naturality
    {N : Type w} [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) :
    tensorLinearMap I n N ∘ₗ f.lTensor (stage I A n) =
      map I f n ∘ₗ tensorLinearMap I n M := sorry

/-- The unbundled ideal-power tensor multiplication commutes with every filtration
inclusion. -/
@[stacks 0G3N "filtration compatibility of unbundled ideal-power tensor multiplication"]
theorem tensorLinearMap_inclusion
    {m n : ℕ} (h : m ≤ n) :
    tensorLinearMap I m M ∘ₗ
        (Submodule.inclusion (Ideal.PowerSubmodule.stage_antitone I h)).rTensor M =
      Submodule.inclusion (Ideal.PowerSubmodule.stage_antitone I h) ∘ₗ
        tensorLinearMap I n M := sorry

/-- Ideal-power tensor multiplication sends a pure tensor to scalar multiplication. -/
@[simp, stacks 0G3N "ideal-power tensor multiplication on pure tensors"]
theorem tensorLinearMap_tmul (a : stage I A n) (m : M) :
    tensorLinearMap I n M (a ⊗ₜ[A] m) = tensorValue I n M a m := sorry

end Linear

section Bundled

variable {A : Type u} [CommRing A]

/-- The bundled multiplication map `(I ^ n A) ⊗[A] M ⟶ I ^ n M`. -/
@[stacks 0G3N "bundled ideal-power tensor multiplication"]
def tensorMap (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    (tensorLeft (stageObj I (ModuleCat.of A A) n)).obj M ⟶ stageObj I M n :=
  ModuleCat.ofHom (tensorLinearMap I n M)

/-- The bundled ideal-power tensor map sends a pure tensor to scalar multiplication. -/
@[simp, stacks 0G3N "bundled ideal-power tensor multiplication on pure tensors"]
theorem tensorMap_tmul (I : Ideal A) (n : ℕ) (M : ModuleCat A)
    (a : stage I A n) (m : M) :
    tensorMap I n M (a ⊗ₜ[A] m) = tensorValue I n M a m := sorry

/-- Forgetting the target adic stage turns `tensorMap` into ordinary scalar multiplication. -/
@[stacks 0G3N "ambient formula for ideal-power tensor multiplication"]
theorem tensorMap_comp_subtype (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    tensorMap I n M ≫ ModuleCat.ofHom (subtype I M n) =
      ModuleCat.ofHom
        (TensorProduct.lift ((LinearMap.lsmul A M).comp (subtype I A n))) := sorry

/-- Ideal-power tensor multiplication is natural in the module. -/
@[stacks 0G3N "naturality of ideal-power tensor multiplication"]
theorem tensorMap_naturality (I : Ideal A) (n : ℕ)
    {M N : ModuleCat A} (f : M ⟶ N) :
    (tensorLeft (stageObj I (ModuleCat.of A A) n)).map f ≫ tensorMap I n N =
      tensorMap I n M ≫ mapObj I f n := sorry

/-- Tensor multiplication as a natural transformation from tensoring with the regular
adic stage to the adic-stage functor. -/
@[stacks 0G3N "ideal-power tensor multiplication natural transformation"]
def tensorNatTrans (I : Ideal A) (n : ℕ) :
    tensorLeft (stageObj I (ModuleCat.of A A) n) ⟶ functor I n where
  app M := tensorMap I n M
  naturality _ _ f := tensorMap_naturality I n f

/-- Tensoring the regular-module inclusion gives the transition between the corresponding
fixed-left tensor functors. -/
@[stacks 0G3N "tensor transition between ideal-power stages"]
def tensorInclusionNatTrans (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    tensorLeft (stageObj I (ModuleCat.of A A) n) ⟶
      tensorLeft (stageObj I (ModuleCat.of A A) m) :=
  (tensoringLeft (ModuleCat A)).map (inclusion I (ModuleCat.of A A) h)

/-- Tensor multiplication commutes with every transition in the adic filtration. -/
@[stacks 0G3N "filtration compatibility of ideal-power tensor multiplication"]
theorem tensorNatTrans_inclusion (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    tensorInclusionNatTrans I h ≫ tensorNatTrans I m =
      tensorNatTrans I n ≫ inclusionNatTrans I h := sorry

/-- The component form of compatibility between tensor multiplication and adic transitions. -/
@[stacks 0G3N "componentwise filtration compatibility of ideal-power tensor multiplication"]
theorem tensorMap_inclusion (I : Ideal A) (M : ModuleCat A)
    {m n : ℕ} (h : m ≤ n) :
    (tensorInclusionNatTrans I h).app M ≫ tensorMap I m M =
      tensorMap I n M ≫ inclusion I M h := sorry

end Bundled

end Ideal.PowerSubmodule
