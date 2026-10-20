module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact Evaluation on Formal Coproducts

This leaf records the exactness properties of `FormalCoproduct.evalOp`.
Fixed-object evaluation is separated from the aggregate functor, and finite
limits are kept independent of the exact-product (`AB4*`) hypothesis.  The
construction is independent of sites, modules, and Cech constructions.
-/

@[expose] public section

open Opposite

universe w v u v' u'

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A]

namespace evalOp

/- The fixed-object evaluator is named once so that preservation statements do
not repeat a long composition and downstream code can refer to its owner. -/
/-- Evaluation of `FormalCoproduct.evalOp` at one formal coproduct. -/
@[stacks 01EJ "formal-coproduct evaluation at an object"]
noncomputable abbrev atObj [HasProducts.{w} A] (X : FormalCoproduct.{w} C) :
    (Cᵒᵖ ⥤ A) ⥤ A :=
  (FormalCoproduct.evalOp.{w} C A) ⋙
    (evaluation (FormalCoproduct.{w} C)ᵒᵖ A).obj (op X)

/-- Fixed formal-coproduct evaluation is exact when its indexing product is exact. -/
@[stacks 01EJ "formal-coproduct evaluation exactness"]
theorem atObj.exact [HasProducts.{w} A]
    (X : FormalCoproduct.{w} C)
    [HasExactLimitsOfShape (Discrete X.I) A] :
    exactFunctor (Cᵒᵖ ⥤ A) A (evalOp.atObj X) := sorry

/-- Fixed formal-coproduct evaluation preserves finite limits as soon as the products exist. -/
@[stacks 01EJ "formal-coproduct evaluation preserves finite limits"]
noncomputable instance atObj.preservesFiniteLimits [HasProducts.{w} A]
    (X : FormalCoproduct.{w} C) :
    PreservesFiniteLimits (evalOp.atObj X : (Cᵒᵖ ⥤ A) ⥤ A) := sorry

/-- Fixed formal-coproduct evaluation preserves finite colimits when its indexing product is
exact. -/
@[stacks 01EJ "formal-coproduct evaluation preserves finite colimits"]
noncomputable instance atObj.preservesFiniteColimits [HasProducts.{w} A]
    (X : FormalCoproduct.{w} C)
    [HasExactLimitsOfShape (Discrete X.I) A] :
    PreservesFiniteColimits (evalOp.atObj X : (Cᵒᵖ ⥤ A) ⥤ A) := sorry

/-- `FormalCoproduct.evalOp` preserves finite limits under the product-existence hypothesis. -/
@[stacks 01EJ "formal-coproduct evaluation functor preserves finite limits"]
noncomputable instance preservesFiniteLimits [HasProducts.{w} A] :
    PreservesFiniteLimits (FormalCoproduct.evalOp.{w} C A) := sorry

/-- `FormalCoproduct.evalOp` preserves finite colimits when products of the indexing size are
exact. -/
@[stacks 01EJ "formal-coproduct evaluation functor preserves finite colimits"]
noncomputable instance preservesFiniteColimits [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (FormalCoproduct.evalOp.{w} C A) := sorry

/-- The aggregate formal-coproduct evaluation functor bundled with exactness. -/
@[stacks 01EJ "bundled exact formal-coproduct evaluation functor"]
noncomputable def exactFunctor [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    (Cᵒᵖ ⥤ A) ⥤ₑ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) :=
  ExactFunctor.of (FormalCoproduct.evalOp.{w} C A)

end evalOp

end CategoryTheory.Limits.FormalCoproduct
