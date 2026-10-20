/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NR

# Endpoint-minimal limit and colimit stability

This file exposes the canonical product and coproduct maps as elimination APIs for morphism
properties stable under limits or colimits of the corresponding discrete shape.  Only the two
displayed (co)products are required to exist.
-/

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- A componentwise morphism in a product-stable morphism property induces a morphism in the
same property between the two displayed products. -/
@[stacks 08NR "endpoint-minimal product-stability API"]
theorem IsStableUnderProductsOfShape.piMap
    {W : MorphismProperty C} {J : Type w} [W.IsStableUnderProductsOfShape J]
    {X Y : J → C} [HasProduct X] [HasProduct Y]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, W (f j)) :
    W (Limits.Pi.map f) := sorry

/-- A componentwise morphism in a coproduct-stable morphism property induces a morphism in the
same property between the two displayed coproducts. -/
@[stacks 08NR "dual endpoint-minimal coproduct-stability API"]
theorem IsStableUnderCoproductsOfShape.sigmaMap
    {W : MorphismProperty C} {J : Type w} [W.IsStableUnderCoproductsOfShape J]
    {X Y : J → C} [HasCoproduct X] [HasCoproduct Y]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, W (f j)) :
    W (Limits.Sigma.map f) := sorry

namespace IsStableUnderBaseChange

/-- Binary products preserve any multiplicative morphism property stable under base change. -/
@[stacks 01G4 "binary products of base-change-stable morphisms"]

theorem prod_map
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {A B K L : C} [HasBinaryProducts C]
    (f : A ⟶ B) (g : K ⟶ L) (hf : P f) (hg : P g) :
    P (Limits.prod.map f g : A ⨯ K ⟶ B ⨯ L) := sorry

end IsStableUnderBaseChange

/-- If every morphism in `P` admits pullbacks against arbitrary arrows, then a particular
`f ∈ P` admits pullbacks along itself in the ordinary, unrestricted sense. -/
@[stacks 02W5 "ordinary pullbacks along a morphism in a pullback-complete property"]
theorem HasPullbacks.hasPullbacksAlong_of_mem
    {P : MorphismProperty C} (h : P.HasPullbacks)
    {X Y : C} {f : X ⟶ Y} (hf : P f) :
    HasPullbacksAlong f := sorry

end CategoryTheory.MorphismProperty
