/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tensor products of K-flat cochain complexes

@stack 0795
@stack 079R
@stack 07A2

K-flatness is closed under the canonical totalized tensor product.  The statement is kept at
the coefficient-category level, independently of modules, sheaves, or derived categories.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CochainComplex.IsKFlat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- The totalized tensor product of two K-flat cochain complexes is K-flat. -/
@[stacks 0795 "K-flat complexes are closed under tensor products",
  stacks 079R "K-flat complexes are closed under tensor products",
  stacks 07A2 "ringed-site K-flat complexes are closed under tensor products"]
theorem tensor {K L : CochainComplex C ℤ}
    (hK : K.IsKFlat) (hL : L.IsKFlat) :
    (HomologicalComplex.tensorObj K L).IsKFlat := sorry

end CochainComplex.IsKFlat

end
