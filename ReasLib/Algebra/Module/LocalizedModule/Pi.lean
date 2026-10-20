/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Finite Products of Modules

This leaf gives the canonical comparison between the localization of a finite
product of modules and the product of their localizations.  The localization
property is supplied directly by Mathlib's `IsLocalizedModule.pi` instance.

@stack 00EK
-/

@[expose] public section

universe u v w x

namespace IsLocalizedModule

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/-- Tag `00EK`: a finite product of arbitrary models of the same module
localization is canonically the localization of the finite product.  The
coordinatewise map is Mathlib's `LinearMap.piMap`; this declaration supplies
the comparison equivalence that is absent from the canonical API. -/
@[stacks 00EK "finite product arbitrary localized module equivalence"]
noncomputable def piEquiv
    (S : Submonoid R) {M : ι → Type v} {N : ι → Type x} [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)] :
    LocalizedModule S (∀ i, M i) ≃ₗ[R] ∀ i, N i :=
  IsLocalizedModule.iso S (.pi fun i ↦ f i ∘ₗ .proj i)

/-- The finite-product localization equivalence agrees with the coordinatewise
map on generators with denominator `1`. -/
@[simp, stacks 00EK "finite product arbitrary localized module equivalence application"]
theorem piEquiv_mk_one
    (S : Submonoid R) {M : ι → Type v} {N : ι → Type x} [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)]
    (x : ∀ i, M i) :
    piEquiv S f (LocalizedModule.mk x 1) = LinearMap.piMap f x := sorry

/-- The finite-product localization equivalence evaluates coordinatewise on
generators with denominator `1`. -/
@[simp, stacks 00EK "finite product arbitrary localized module coordinate application"]
theorem piEquiv_mk_one_apply
    (S : Submonoid R) {M : ι → Type v} {N : ι → Type x} [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)]
    (x : ∀ i, M i) (i : ι) :
    piEquiv S f (LocalizedModule.mk x 1) i = f i (x i) := sorry

end IsLocalizedModule

namespace LocalizedModule

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/-- Tag `00EK`: the coordinatewise canonical map from a product of modules to
the product of their localizations. -/
@[stacks 00EK "finite product localized module map"]
noncomputable def piMkLinearMap
    (S : Submonoid R) (M : ι → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (∀ i, M i) →ₗ[R] ∀ i, LocalizedModule S (M i) :=
  LinearMap.piMap fun i ↦ LocalizedModule.mkLinearMap S (M i)

/-- For a finite index type, `piMkLinearMap` is a localization map by
Mathlib's finite-product localization instance. -/
@[stacks 00EK "finite product localized module property"]
instance piMkLinearMap.isLocalizedModule
    (S : Submonoid R) (M : ι → Type v) [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    IsLocalizedModule S (piMkLinearMap S M) :=
  IsLocalizedModule.pi S fun i ↦ LocalizedModule.mkLinearMap S (M i)

/-- Tag `00EK`: localization commutes with a finite product of modules. -/
@[stacks 00EK "finite product localized module equivalence"]
noncomputable def piLinearEquiv
    (S : Submonoid R) (M : ι → Type v) [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    LocalizedModule S (∀ i, M i) ≃ₗ[Localization S]
      ∀ i, LocalizedModule S (M i) :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.piEquiv S fun i ↦ LocalizedModule.mkLinearMap S (M i))

/-- The coordinatewise localization map evaluates by applying the canonical
localization map in the selected coordinate. -/
@[simp, stacks 00EK "finite product localized module map application"]
theorem piMkLinearMap_apply
    (S : Submonoid R) (M : ι → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : ∀ i, M i) (i : ι) :
    piMkLinearMap S M x i = LocalizedModule.mkLinearMap S (M i) (x i) := sorry

/-- The finite-product localization equivalence sends a localized product
generator to the tuple of localized coordinate generators. -/
@[simp, stacks 00EK "finite product localized module equivalence application"]
theorem piLinearEquiv_apply_mk
    (S : Submonoid R) (M : ι → Type v) [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (x : ∀ i, M i) (s : S) (i : ι) :
    piLinearEquiv S M (LocalizedModule.mk x s) i = LocalizedModule.mk (x i) s := sorry

/-- The finite-product localization comparison is natural for coordinatewise
linear maps. -/
@[stacks 00EK "finite product localized module naturality"]
theorem piLinearEquiv_naturality
    (S : Submonoid R) {M : ι → Type v} {N : ι → Type*} [Finite ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) :
    (LinearMap.piMap fun i ↦ LocalizedModule.map S (f i)).comp
        (piLinearEquiv S M).toLinearMap =
      (piLinearEquiv S N).toLinearMap.comp
        (LocalizedModule.map S (LinearMap.piMap f)) := sorry

end LocalizedModule
