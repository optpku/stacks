/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products and pseudo-coherent derived tensor products

This leaf owns the product-preservation direction of the pseudo-coherence criterion.  Its
canonical comparison lives entirely in the derived category: the fixed-left view of the
two-variable derived tensor functor is applied to the degree-zero image of a family of modules.
This is the exact interface needed by homotopy-limit preservation.
@stack 0CYB
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [CommRing R]

/-- Stacks 0CYB: fixed-left tensoring by a pseudo-coherent derived `R`-module preserves the
product of any family of degree-zero modules.  The comparison is formed in `D(R)`, so it can be
used directly as the product-preservation input for a Milnor triangle. -/
@[stacks 0CYB "pseudo-coherent derived tensor preserves products"]
theorem piComparison_single_isIso
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : K.IsPseudoCoherent)
    {J : Type w} (Q : J → ModuleCat.{u} R)
    [HasProduct (fun j ↦
      ModuleCat.single0Functor.obj (Q j))]
    [HasProduct (fun j ↦
      (DerivedTensor.Bifunctor.leftFunctor K).obj
        (ModuleCat.single0Functor.obj (Q j)))] :
    IsIso (piComparison
      (DerivedTensor.Bifunctor.leftFunctor K)
      (fun j ↦ ModuleCat.single0Functor.obj (Q j))) := sorry

/-- The product-comparison criterion is exposed as a preservation proposition so a
homotopy-limit proof can install exactly the family-level fact it needs. -/
@[stacks 0CYB "pseudo-coherent tensor preserves the selected product"]
theorem preservesLimit_single_of_piComparison_isIso
    {K : DerivedCategory (ModuleCat.{u} R)}
    {J : Type w} (Q : J → ModuleCat.{u} R)
    [HasProduct (fun j ↦ ModuleCat.single0Functor.obj (Q j))]
    [HasProduct (fun j ↦
      (DerivedTensor.Bifunctor.leftFunctor K).obj
        (ModuleCat.single0Functor.obj (Q j)))]
    [IsIso (piComparison
      (DerivedTensor.Bifunctor.leftFunctor K)
      (fun j ↦ ModuleCat.single0Functor.obj (Q j)))] :
    PreservesLimit
      (Discrete.functor (fun j ↦ ModuleCat.single0Functor.obj (Q j)))
      (DerivedTensor.Bifunctor.leftFunctor K) := sorry

/-- A pseudo-coherent fixed left factor preserves every selected product of degree-zero
module complexes. -/
@[stacks 0CYB "pseudo-coherent tensor preserves degree-zero products"]
theorem preservesLimit_single_of_isPseudoCoherent
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : K.IsPseudoCoherent)
    {J : Type w} (Q : J → ModuleCat.{u} R)
    [HasProduct (fun j ↦ ModuleCat.single0Functor.obj (Q j))]
    [HasProduct (fun j ↦
      (DerivedTensor.Bifunctor.leftFunctor K).obj
        (ModuleCat.single0Functor.obj (Q j)))] :
    PreservesLimit
      (Discrete.functor (fun j ↦ ModuleCat.single0Functor.obj (Q j)))
      (DerivedTensor.Bifunctor.leftFunctor K) := sorry

end CategoryTheory.DerivedCategory.IsPseudoCoherent
