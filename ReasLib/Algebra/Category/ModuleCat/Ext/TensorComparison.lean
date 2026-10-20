/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.LinearAlgebra.TensorProduct.Contraction
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor comparison maps for Hom and Ext

The canonical comparison tensors a Hom or Ext class with a flat module and moves that tensor
factor to the target module.

@stack 087Q
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u

-- Local instance justification (instance diamond): select the standard derived-category model
-- only for this Ext tensor comparison.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat.Ext.TensorComparison

variable {R : Type u} [CommRing R]

/-- The degree-zero Ext class of the canonical map `n ↦ n ⊗ l`, linear in `l`. -/
@[stacks 087Q "degree-zero tensor class"]
noncomputable def degreeZeroTensorClass (N L : ModuleCat.{u} R) :
    L →ₗ[R] Abelian.Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 :=
  (((Abelian.Ext.linearEquiv₀ :
      Abelian.Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 ≃ₗ[R]
        (N ⟶ ModuleCat.of R (TensorProduct R N L))).symm.toLinearMap).comp
    (((ModuleCat.homLinearEquiv :
        (N ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (N →ₗ[R] TensorProduct R N L)).symm.toLinearMap).comp
      ((TensorProduct.mk R N L).flip)))

/-- The canonical map `Ext^i_R(M, N) ⊗_R L → Ext^i_R(M, N ⊗_R L)`. -/
@[stacks 087Q "Ext tensor comparison"]
noncomputable def extComparison (M N L : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.of R (TensorProduct R (Abelian.Ext.{u} M N i) L) ⟶
      ModuleCat.of R (Abelian.Ext.{u} M (ModuleCat.of R (TensorProduct R N L)) i) :=
  ModuleCat.ofHom <|
    TensorProduct.lift <|
      LinearMap.compl₂
        (Abelian.Ext.bilinearCompOfLinear R M N
          (ModuleCat.of R (TensorProduct R N L)) i 0 i (add_zero i))
        (degreeZeroTensorClass N L)

/-- The canonical map `Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)`. -/
@[stacks 087Q "Hom tensor comparison"]
noncomputable def homComparison (M N L : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R (M ⟶ N) L) ⟶
      ModuleCat.of R (M ⟶ ModuleCat.of R (TensorProduct R N L)) :=
  ModuleCat.ofHom <|
    ((ModuleCat.homLinearEquiv :
        (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (M →ₗ[R] TensorProduct R N L)).symm.toLinearMap) ∘ₗ
      TensorProduct.rTensorHomToHomRTensor (.id R) M N L ∘ₗ
      (LinearEquiv.rTensor L ModuleCat.homLinearEquiv).toLinearMap

/-- Lemma 15.66.3 (1), linear-map form: the raw tensor-Hom comparison is bijective for a
finitely presented source and a flat tensor factor. -/
@[stacks 087Q "Lemma 15.66.3 (1), linear-map form"]
theorem rTensorHomToHomRTensor_bijective_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M N L) := sorry
-- Proof strategy: choose a finite free presentation of `M`, compare the two contravariant Hom
-- rows, use flatness of `L` to preserve exactness after tensoring, and use the finite-projective
-- tensor-Hom equivalence on both free presentation terms.

/-- Lemma 15.66.3 (1): the Hom tensor comparison is an isomorphism for a finitely presented
source and a flat tensor factor. -/
@[stacks 087Q "Lemma 15.66.3 (1)"]
theorem homComparison_isIso_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    IsIso (homComparison M N L) := sorry
-- Proof strategy: unfold `homComparison`, observe that its underlying linear map is the raw
-- tensor-Hom comparison conjugated by `ModuleCat.homLinearEquiv`, and apply
-- `rTensorHomToHomRTensor_bijective_of_finitePresentation` and `isIso_iff_bijective`.

/-- Lemma 15.66.3 (2): the Ext tensor comparison in degree `i < m` is an isomorphism when the
source is `(-m)`-pseudo-coherent and the tensor factor is flat. -/
@[stacks 087Q "Lemma 15.66.3 (2)"]
theorem extComparison_isIso_of_isMPseudoCoherent
    (M N L : ModuleCat.{u} R) (m i : ℕ) [Module.Flat R L]
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (extComparison M N L i) := sorry
-- Proof strategy: choose a resolution of `M` that is finite free through degree `m`, compare its
-- two Hom complexes termwise using the tensor-Hom isomorphism, commute cohomology with tensoring
-- by the flat module `L`, and identify the induced map with `extComparison` via Yoneda product.

end CategoryTheory.ModuleCat.Ext.TensorComparison
