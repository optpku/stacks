/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MA

# Differential of a tensor product of cochain complexes

This leaf exposes the summandwise Leibniz formula for the canonical tensor totalization.  The
underlying differential and summand inclusions remain the Mathlib owners `tensorObj` and
`ιTensorObj`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [MonoidalPreadditive C]
variable {K L : CochainComplex C ℤ} [HasTensor K L]

/-- 20.25.3.1 (Tag 07MA): on a bidegree `(p,q)` summand, the tensor differential is
`d_K ⊗ 1 + (-1)^p (1 ⊗ d_L)`. -/
@[stacks 07MA, reassoc]
theorem ιTensorObj_d (p q : ℤ) :
    ιTensorObj K L p q (p + q) rfl ≫ (tensorObj K L).d (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          ιTensorObj K L (p + 1) q (p + q + 1) (add_right_comm p 1 q) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            ιTensorObj K L p (q + 1) (p + q + 1) (add_assoc p q 1).symm) := sorry

end HomologicalComplex

end
