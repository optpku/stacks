/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise

/-!
# Tensor products of bounded termwise complexes

This file isolates the generic finite-antidiagonal argument for tensor products of bounded
cochain complexes.  The termwise property is required only to be closed under finite coproducts,
isomorphisms, and tensor products.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- Lower bounds add under the total tensor product of cochain complexes. -/
theorem tensorObj_isStrictlyGE {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]
    {a b : ℤ} (hK : K.IsStrictlyGE a) (hL : L.IsStrictlyGE b) :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj K L) (a + b) := sorry

/-- Upper bounds add under the total tensor product of cochain complexes. -/
theorem tensorObj_isStrictlyLE {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]
    {a b : ℤ} (hK : K.IsStrictlyLE a) (hL : L.IsStrictlyLE b) :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj K L) (a + b) := sorry

/-- The total tensor product of bounded cochain complexes is bounded. -/
theorem tensorObj_bounded {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (HomologicalComplex.tensorObj K L) := sorry

variable (P : ObjectProperty C) [P.IsClosedUnderFiniteCoproducts]
variable [P.IsClosedUnderIsomorphisms] [ObjectProperty.TensorLE P P P]

/-- The total tensor product is termwise in `P` when both bounded inputs are termwise in `P`. -/
theorem termsIn_tensorObj {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]
    (hKbounded : CochainComplex.bounded C K) (hLbounded : CochainComplex.bounded C L)
    (hK : CochainComplex.termsIn P K) (hL : CochainComplex.termsIn P L) :
    CochainComplex.termsIn P (HomologicalComplex.tensorObj K L) := sorry

/-- The total tensor product preserves bounded complexes termwise in `P`. -/
theorem boundedTermsIn_tensorObj {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]
    (hK : boundedTermsIn P K) (hL : boundedTermsIn P L) :
    boundedTermsIn P (HomologicalComplex.tensorObj K L) := sorry

end CochainComplex
