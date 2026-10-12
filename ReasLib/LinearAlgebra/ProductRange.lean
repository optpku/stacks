/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Product ranges of linear maps

This module owns the elementary linear-algebra condition that an injective map into a binary
product has product-shaped range, together with its scalar-extension form.  It is independent of
the geometric applications that first use the condition.
@stack 0F7Z
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace LinearMap

section Semiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N₁ : Type v} [AddCommMonoid N₁] [Module R N₁]
variable {N₂ : Type v} [AddCommMonoid N₂] [Module R N₂]

/-- The base change of a pair-valued map, with the tensor product of the target product
identified with the product of the two base-changed targets. -/
abbrev baseChangePairMap (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] :
    B ⊗[R] M →ₗ[B] (B ⊗[R] N₁) × (B ⊗[R] N₂) :=
  (TensorProduct.prodRight R B B N₁ N₂).toLinearMap ∘ₗ s.baseChange B

/-- The base-changed pair map sends a pure tensor to the pair of pure tensors formed from the
two coordinate maps. -/
@[simp]
theorem baseChangePairMap_tmul (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] (b : B) (m : M) :
    s.baseChangePairMap B (b ⊗ₜ m) =
      (b ⊗ₜ ((LinearMap.fst R N₁ N₂).comp s) m,
        b ⊗ₜ ((LinearMap.snd R N₁ N₂).comp s) m) := sorry

/-- Distributing scalar extension over the binary target product identifies the base-changed pair
map with the product of the base-changed coordinate maps. -/
@[simp]
theorem baseChangePairMap_eq_prod (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] :
    s.baseChangePairMap B =
      LinearMap.prod (((LinearMap.fst R N₁ N₂).comp s).baseChange B)
        (((LinearMap.snd R N₁ N₂).comp s).baseChange B) := sorry

/-- The first coordinate of the base-changed pair map is the base change of the first coordinate
of the original map. -/
@[simp]
theorem fst_comp_baseChangePairMap (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] :
    (LinearMap.fst B (B ⊗[R] N₁) (B ⊗[R] N₂)).comp (s.baseChangePairMap B) =
      ((LinearMap.fst R N₁ N₂).comp s).baseChange B := sorry

/-- The second coordinate of the base-changed pair map is the base change of the second coordinate
of the original map. -/
@[simp]
theorem snd_comp_baseChangePairMap (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] :
    (LinearMap.snd B (B ⊗[R] N₁) (B ⊗[R] N₂)).comp (s.baseChangePairMap B) =
      ((LinearMap.snd R N₁ N₂).comp s).baseChange B := sorry

/-- The range of `s` is the product of the ranges of its two coordinate maps. -/
def rangeIsProduct (s : M →ₗ[R] N₁ × N₂) : Prop :=
  LinearMap.range s =
    (LinearMap.range ((LinearMap.fst R N₁ N₂).comp s)).prod
      (LinearMap.range ((LinearMap.snd R N₁ N₂).comp s))

/-- An injective pair-valued map identifies its source with a product of submodules of its two
target factors.  This presentation retains the explicitly chosen submodules when they are useful
in a construction. -/
def identifiesWithProdSubmodules (s : M →ₗ[R] N₁ × N₂) : Prop :=
  ∃ P₁ : Submodule R N₁,
    ∃ P₂ : Submodule R N₂,
      Function.Injective s ∧ LinearMap.range s = P₁.prod P₂

/-- The existential product-submodule formulation is equivalent to injectivity together with the
canonical coordinate-range formulation `rangeIsProduct`. -/
theorem identifiesWithProdSubmodules_iff_rangeIsProduct (s : M →ₗ[R] N₁ × N₂) :
    s.identifiesWithProdSubmodules ↔ Function.Injective s ∧ s.rangeIsProduct := sorry

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module R N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module R N₂]

/-- If every first-coordinate value can be represented while the second coordinate vanishes,
then the range of a pair-valued map is the product of its coordinate ranges. -/
@[stacks 0F7Z "product range criterion"]
theorem rangeIsProduct_of_fst_range_eq (s : M →ₗ[R] N₁ × N₂)
    (hfst :
      LinearMap.range
          (((LinearMap.fst R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.fst R N₁ N₂).comp s)) :
    s.rangeIsProduct := sorry

/-- A pair-valued map has product-shaped range exactly when every value of its first coordinate
can be represented by an element on which the second coordinate vanishes. -/
theorem rangeIsProduct_iff_fst_range_eq (s : M →ₗ[R] N₁ × N₂) :
    s.rangeIsProduct ↔
      LinearMap.range
          (((LinearMap.fst R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.fst R N₁ N₂).comp s) := sorry

/-- If every second-coordinate value can be represented while the first coordinate vanishes,
then the range of a pair-valued map is the product of its coordinate ranges. -/
theorem rangeIsProduct_of_snd_range_eq (s : M →ₗ[R] N₁ × N₂)
    (hsnd :
      LinearMap.range
          (((LinearMap.snd R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.fst R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.snd R N₁ N₂).comp s)) :
    s.rangeIsProduct := sorry

/-- A pair-valued map has product-shaped range exactly when every value of its second coordinate
can be represented by an element on which the first coordinate vanishes. -/
theorem rangeIsProduct_iff_snd_range_eq (s : M →ₗ[R] N₁ × N₂) :
    s.rangeIsProduct ↔
      LinearMap.range
          (((LinearMap.snd R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.fst R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.snd R N₁ N₂).comp s) := sorry

/-- An injective pair-valued map identifies its source with a product of submodules when every
first-coordinate value has a representative on which the second coordinate vanishes. -/
theorem identifiesWithProdSubmodules_of_fst_range_eq (s : M →ₗ[R] N₁ × N₂)
    (hs : Function.Injective s)
    (hfst :
      LinearMap.range
          (((LinearMap.fst R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.fst R N₁ N₂).comp s)) :
    s.identifiesWithProdSubmodules := sorry

/-- An injective pair-valued map identifies its source with a product of submodules exactly when
every first-coordinate value has a representative on which the second coordinate vanishes. -/
theorem identifiesWithProdSubmodules_iff_fst_range_eq (s : M →ₗ[R] N₁ × N₂) :
    s.identifiesWithProdSubmodules ↔
      Function.Injective s ∧
        LinearMap.range
            (((LinearMap.fst R N₁ N₂).comp s).domRestrict
              (LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s))) =
          LinearMap.range ((LinearMap.fst R N₁ N₂).comp s) := sorry

/-- An injective pair-valued map identifies its source with a product of submodules when every
second-coordinate value has a representative on which the first coordinate vanishes. -/
theorem identifiesWithProdSubmodules_of_snd_range_eq (s : M →ₗ[R] N₁ × N₂)
    (hs : Function.Injective s)
    (hsnd :
      LinearMap.range
          (((LinearMap.snd R N₁ N₂).comp s).domRestrict
            (LinearMap.ker ((LinearMap.fst R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.snd R N₁ N₂).comp s)) :
    s.identifiesWithProdSubmodules := sorry

/-- An injective pair-valued map identifies its source with a product of submodules exactly when
every second-coordinate value has a representative on which the first coordinate vanishes. -/
theorem identifiesWithProdSubmodules_iff_snd_range_eq (s : M →ₗ[R] N₁ × N₂) :
    s.identifiesWithProdSubmodules ↔
      Function.Injective s ∧
        LinearMap.range
            (((LinearMap.snd R N₁ N₂).comp s).domRestrict
              (LinearMap.ker ((LinearMap.fst R N₁ N₂).comp s))) =
          LinearMap.range ((LinearMap.snd R N₁ N₂).comp s) := sorry

end Ring

section Semiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N₁ : Type v} [AddCommMonoid N₁] [Module R N₁]
variable {N₂ : Type v} [AddCommMonoid N₂] [Module R N₂]

/-- Identifying the source and the two target factors by linear equivalences preserves the
property of identifying the source with a product of submodules. -/
theorem identifiesWithProdSubmodules_congr
    {M' N₁' N₂' : Type w}
    [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N₁'] [Module R N₁']
    [AddCommMonoid N₂'] [Module R N₂']
    (s : M →ₗ[R] N₁ × N₂) (t : M' →ₗ[R] N₁' × N₂')
    (eM : M ≃ₗ[R] M') (e₁ : N₁ ≃ₗ[R] N₁') (e₂ : N₂ ≃ₗ[R] N₂')
    (h : (LinearEquiv.prodCongr e₁ e₂).toLinearMap.comp s =
      t.comp eM.toLinearMap) :
    s.identifiesWithProdSubmodules ↔ t.identifiesWithProdSubmodules := sorry

/-- The base-changed pair map has product-shaped range. -/
def baseChangeRangeIsProduct (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] : Prop :=
  (baseChangePairMap s B).rangeIsProduct

/-- After base change, the pair-valued map identifies its source with a product of submodules of
the two base-changed target factors. -/
def baseChangeIdentifiesWithProdSubmodules (s : M →ₗ[R] N₁ × N₂) (B : Type w)
    [CommSemiring B] [Algebra R B] : Prop :=
  (baseChangePairMap s B).identifiesWithProdSubmodules

/-- The base-changed existential product-submodule formulation is equivalent to injectivity and
the canonical product-range condition after base change. -/
theorem baseChangeIdentifiesWithProdSubmodules_iff_rangeIsProduct
    (s : M →ₗ[R] N₁ × N₂) (B : Type w) [CommSemiring B] [Algebra R B] :
    s.baseChangeIdentifiesWithProdSubmodules B ↔
      Function.Injective (s.baseChangePairMap B) ∧ s.baseChangeRangeIsProduct B := sorry

end Semiring

end LinearMap
