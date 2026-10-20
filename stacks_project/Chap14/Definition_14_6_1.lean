/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Product
import StacksCheckRecall

/-!
@stack 016Q
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U V : SimplicialObject C)
variable [Limits.FunctorCategory.Binary.HasPointwiseProduct U V]
variable {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))

/- Definition 14.6.1 (1): the product simplicial object is the canonical functor-category
product, and evaluation identifies it with the degreewise product. -/
#check (Limits.FunctorCategory.pointwise.binaryProduct U V :
  HasBinaryProduct U V)

@[stacks 016Q "Definition 14.6.1 (1)"]
#check (Limits.FunctorCategory.evaluation.productIso U V (op ⦋n⦌) :
  (U ⨯ V) _⦋n⦌ ≅ U _⦋n⦌ ⨯ V _⦋n⦌)

/- Definition 14.6.1 (2): every face map is the product of the corresponding face maps. -/
@[stacks 016Q "Definition 14.6.1 (2)"]
#check (Limits.FunctorCategory.evaluation.productIso.map U V (SimplexCategory.δ i).op :
  (U ⨯ V).δ i ≫
      (Limits.FunctorCategory.evaluation.productIso U V (op ⦋n⦌)).hom =
    (Limits.FunctorCategory.evaluation.productIso U V (op ⦋n + 1⦌)).hom ≫
      prod.map (U.δ i) (V.δ i))

/- Definition 14.6.1 (3): every degeneracy map is the product of the corresponding degeneracy
maps. -/
@[stacks 016Q "Definition 14.6.1 (3)"]
#check (Limits.FunctorCategory.evaluation.productIso.map U V (SimplexCategory.σ j).op :
  (U ⨯ V).σ j ≫
      (Limits.FunctorCategory.evaluation.productIso U V (op ⦋n + 1⦌)).hom =
    (Limits.FunctorCategory.evaluation.productIso U V (op ⦋n⦌)).hom ≫
      prod.map (U.σ j) (V.σ j))

end CategoryTheory.SimplicialObject
