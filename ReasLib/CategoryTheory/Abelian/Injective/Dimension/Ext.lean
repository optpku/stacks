module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Injective Dimension from Ext Vanishing

This file packages fixed-target and uniform degreewise Ext-vanishing criteria
for strict bounds on injective dimension.
-/

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.HasInjectiveDimensionLT

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [EnoughProjectives C]

/-- If every degree-`p` Ext group with fixed target `A` is subsingleton, then
`A` has injective dimension strictly less than `p`.

The `[EnoughProjectives C]` hypothesis is essential: it supplies the dimension-shifting
step used by the canonical mathlib criterion `hasInjectiveDimensionLT_of_enoughProjectives`. -/
theorem of_ext_vanishing
    (A : C) (p : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p)) :
    HasInjectiveDimensionLT A p :=
  hasInjectiveDimensionLT_of_enoughProjectives A p hExt

/-- Lemma 13.27.8 (Stacks `0EWW`): uniform vanishing of degree-`p` Ext groups
gives injective dimension strictly less than `p` for every target object.

As in the fixed-target form, enough projectives are required for dimension shifting. -/
@[stacks 0EWW]
theorem of_uniform_ext
    (p : ℕ) (hExt : ∀ A B : C, Subsingleton (Ext B A p)) (A : C) :
    HasInjectiveDimensionLT A p :=
  of_ext_vanishing A p (fun B ↦ hExt A B)

end CategoryTheory.HasInjectiveDimensionLT
