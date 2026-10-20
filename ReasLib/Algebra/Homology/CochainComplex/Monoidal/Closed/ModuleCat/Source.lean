/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat
public import ReasLib.CategoryTheory.Monoidal.Closed.Source

/-!
# Source-order operations on module Hom complexes

The generic closed-monoidal source-order maps transport canonically across the natural
comparison between ambient and module-valued Hom complexes. This leaf exposes the strict
module-complex forms used in calculations while retaining the generic constructions as their
single conceptual owners.

@stack 0A5Y
@stack 0BYM
@stack 0A62
@stack 0A8I
@stack 0A60
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CochainComplex.HomComplex

namespace CategoryTheory.CochainComplex.InternalHom.Module

variable {R : Type u} [CommRing R]

/-- Lemma 15.72.1 (0A5Y): currying identifies an iterated module-valued Hom complex with the
Hom complex out of the tensor product. -/
@[stacks 0A5Y "currying isomorphism of module-valued Hom complexes"]
noncomputable def tensorIso
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    moduleComplex R K (moduleComplex R L M) ≅ moduleComplex R (K ⊗ L) M :=
  (moduleComplexIso K (moduleComplex R L M)).symm ≪≫
    (ihom K).mapIso (moduleComplexIso L M).symm ≪≫
      MonoidalClosed.internalHomTensorIso K L M ≪≫
        moduleComplexIso (K ⊗ L) M

/-- The currying isomorphism is contravariantly natural in its left tensor factor. -/
theorem tensorIso_natural_left
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K) :
    CochainComplex.HomComplex.map R f (𝟙 (moduleComplex R L M)) ≫
        (tensorIso K' L M).hom =
      (tensorIso K L M).hom ≫
        CochainComplex.HomComplex.map R (f ▷ L) (𝟙 M) := sorry

/-- The currying isomorphism is contravariantly natural in its middle source variable. -/
theorem tensorIso_natural_middle
    (K : CochainComplex (ModuleCat R) ℤ)
    {L L' M : CochainComplex (ModuleCat R) ℤ} (f : L' ⟶ L) :
    CochainComplex.HomComplex.map R (𝟙 K)
          (CochainComplex.HomComplex.map R f (𝟙 M)) ≫
        (tensorIso K L' M).hom =
      (tensorIso K L M).hom ≫
        CochainComplex.HomComplex.map R (K ◁ f) (𝟙 M) := sorry

/-- The currying isomorphism is covariantly natural in its target variable. -/
theorem tensorIso_natural_right
    (K L : CochainComplex (ModuleCat R) ℤ)
    {M M' : CochainComplex (ModuleCat R) ℤ} (f : M ⟶ M') :
    CochainComplex.HomComplex.map R (𝟙 K)
          (CochainComplex.HomComplex.map R (𝟙 L) f) ≫
        (tensorIso K L M').hom =
      (tensorIso K L M).hom ≫
        CochainComplex.HomComplex.map R (𝟙 (K ⊗ L)) f := sorry

/-- Lemma 15.72.4 (0BYM): tensoring a module-valued Hom complex maps canonically into the Hom
complex whose target has been tensored. -/
@[stacks 0BYM "tensor comparison for module-valued Hom complexes"]
noncomputable def tensor
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    K ⊗ moduleComplex R M L ⟶ moduleComplex R M (K ⊗ L) :=
  (𝟙 K ⊗ₘ (moduleComplexIso M L).inv) ≫
    MonoidalClosed.Source.tensor K L M ≫
      (moduleComplexIso M (K ⊗ L)).hom

/-- The tensor comparison is covariantly natural in the tensor factor. -/
theorem tensor_natural_tensor
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ K') :
    (f ⊗ₘ 𝟙 (moduleComplex R M L)) ≫ tensor K' L M =
      tensor K L M ≫
        CochainComplex.HomComplex.map R (𝟙 M) (f ▷ L) := sorry

/-- The tensor comparison is covariantly natural in its target complex. -/
theorem tensor_natural_target
    (K M : CochainComplex (ModuleCat R) ℤ)
    {L L' : CochainComplex (ModuleCat R) ℤ} (f : L ⟶ L') :
    (𝟙 K ⊗ₘ CochainComplex.HomComplex.map R (𝟙 M) f) ≫
        tensor K L' M =
      tensor K L M ≫
        CochainComplex.HomComplex.map R (𝟙 M) (K ◁ f) := sorry

/-- The tensor comparison is contravariantly natural in its source complex. -/
theorem tensor_natural_source
    (K L : CochainComplex (ModuleCat R) ℤ)
    {M M' : CochainComplex (ModuleCat R) ℤ} (f : M ⟶ M') :
    (𝟙 K ⊗ₘ CochainComplex.HomComplex.map R f (𝟙 L)) ≫
        tensor K L M =
      tensor K L M' ≫
        CochainComplex.HomComplex.map R f (𝟙 (K ⊗ L)) := sorry

/-- Lemma 15.72.5 (0A62): the tensor-internal-Hom unit with its codomain expressed as the
module-valued Hom complex. -/
@[stacks 0A62 "tensor unit for module-valued Hom complexes"]
noncomputable def tensorUnit
    (K L : CochainComplex (ModuleCat R) ℤ) :
    K ⟶ moduleComplex R L (K ⊗ L) :=
  MonoidalClosed.tensorInternalHomUnit K L ≫
    (moduleComplexIso L (K ⊗ L)).hom

/-- The tensor-internal-Hom unit is natural in the tensor factor. -/
theorem tensorUnit_natural_left
    {K K' L : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ K') :
    f ≫ tensorUnit K' L =
      tensorUnit K L ≫
        CochainComplex.HomComplex.map R (𝟙 L) (f ▷ L) := sorry

/-- The tensor-internal-Hom unit is natural in the internal-Hom source. -/
theorem tensorUnit_natural_right
    (K : CochainComplex (ModuleCat R) ℤ)
    {L L' : CochainComplex (ModuleCat R) ℤ} (f : L ⟶ L') :
    tensorUnit K L' ≫
        CochainComplex.HomComplex.map R f (𝟙 (K ⊗ L')) =
      tensorUnit K L ≫
        CochainComplex.HomComplex.map R (𝟙 L) (K ◁ f) := sorry

/-- Lemma 15.72.3 (0A8I): source-order composition of module-valued Hom complexes. -/
@[stacks 0A8I "source-order composition of module-valued Hom complexes"]
noncomputable def comp
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    moduleComplex R L M ⊗ moduleComplex R K L ⟶ moduleComplex R K M :=
  ((moduleComplexIso L M).inv ⊗ₘ (moduleComplexIso K L).inv) ≫
    MonoidalClosed.Source.comp K L M ≫ (moduleComplexIso K M).hom

/-- Composition is covariantly natural in the target complex. -/
theorem comp_natural_target
    (K L : CochainComplex (ModuleCat R) ℤ)
    {M M' : CochainComplex (ModuleCat R) ℤ} (f : M ⟶ M') :
    (CochainComplex.HomComplex.map R (𝟙 L) f ⊗ₘ
          𝟙 (moduleComplex R K L)) ≫ comp K L M' =
      comp K L M ≫ CochainComplex.HomComplex.map R (𝟙 K) f := sorry

/-- Composition is contravariantly natural in the source complex. -/
theorem comp_natural_source
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ K') :
    (𝟙 (moduleComplex R L M) ⊗ₘ
          CochainComplex.HomComplex.map R f (𝟙 L)) ≫ comp K L M =
      comp K' L M ≫ CochainComplex.HomComplex.map R f (𝟙 M) := sorry

/-- The two variances of the middle complex give the same composition map. -/
theorem comp_natural_middle
    (K : CochainComplex (ModuleCat R) ℤ)
    {L L' M : CochainComplex (ModuleCat R) ℤ} (f : L ⟶ L') :
    (CochainComplex.HomComplex.map R f (𝟙 M) ⊗ₘ
          𝟙 (moduleComplex R K L)) ≫ comp K L M =
      (𝟙 (moduleComplex R L' M) ⊗ₘ
          CochainComplex.HomComplex.map R (𝟙 K) f) ≫ comp K L' M := sorry

/-- Lemma 15.72.6 (0A60): the canonical map from a tensor product to an iterated
module-valued Hom complex. -/
@[stacks 0A60 "tensor-to-iterated module-valued Hom comparison"]
noncomputable def iterated
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    moduleComplex R L M ⊗ K ⟶ moduleComplex R (moduleComplex R K L) M :=
  ((moduleComplexIso L M).inv ▷ K) ≫
    MonoidalClosed.Source.Iterated.map K L M ≫
      (MonoidalClosed.pre (moduleComplexIso K L).inv).app M ≫
        (moduleComplexIso (moduleComplex R K L) M).hom

/-- The iterated comparison is covariantly natural in the tensor-factor complex. -/
theorem iterated_natural_source
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K) :
    (𝟙 (moduleComplex R L M) ⊗ₘ f) ≫ iterated K L M =
      iterated K' L M ≫
        CochainComplex.HomComplex.map R
          (CochainComplex.HomComplex.map R f (𝟙 L)) (𝟙 M) := sorry

/-- The iterated comparison is contravariantly natural in the middle complex. -/
theorem iterated_natural_middle
    (K : CochainComplex (ModuleCat R) ℤ)
    {L L' M : CochainComplex (ModuleCat R) ℤ} (f : L ⟶ L') :
    (CochainComplex.HomComplex.map R f (𝟙 M) ⊗ₘ 𝟙 K) ≫ iterated K L M =
      iterated K L' M ≫
        CochainComplex.HomComplex.map R
          (CochainComplex.HomComplex.map R (𝟙 K) f) (𝟙 M) := sorry

/-- The iterated comparison is covariantly natural in the target complex. -/
theorem iterated_natural_target
    (K L : CochainComplex (ModuleCat R) ℤ)
    {M M' : CochainComplex (ModuleCat R) ℤ} (f : M ⟶ M') :
    (CochainComplex.HomComplex.map R (𝟙 L) f ⊗ₘ 𝟙 K) ≫ iterated K L M' =
      iterated K L M ≫
        CochainComplex.HomComplex.map R (𝟙 (moduleComplex R K L)) f := sorry

end CategoryTheory.CochainComplex.InternalHom.Module
