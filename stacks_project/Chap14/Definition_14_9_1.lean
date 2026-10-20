/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Product
import StacksCheckRecall

/-!
@stack 016Z
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U V : CosimplicialObject C)
variable [Limits.FunctorCategory.Binary.HasPointwiseProduct U V]
variable {m n : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌)

/- Definition 14.9.1 (1): the product cosimplicial object is computed degreewise. -/
#check (pointwise.binaryProduct U V : HasBinaryProduct U V)

@[stacks 016Z "Definition 14.9.1 (1)"]
#check (Limits.FunctorCategory.evaluation.productIso U V ⦋n⦌ :
  (U ⨯ V) ^⦋n⦌ ≅ U ^⦋n⦌ ⨯ V ^⦋n⦌)

/- Definition 14.9.1 (2): every structure map is the product of the corresponding component
maps. -/
@[stacks 016Z "Definition 14.9.1 (2)"]
#check (Limits.FunctorCategory.evaluation.productIso.map U V φ :
  (U ⨯ V).map φ ≫ (Limits.FunctorCategory.evaluation.productIso U V ⦋m⦌).hom =
    (Limits.FunctorCategory.evaluation.productIso U V ⦋n⦌).hom ≫
      prod.map (U.map φ) (V.map φ))

end CategoryTheory.CosimplicialObject
