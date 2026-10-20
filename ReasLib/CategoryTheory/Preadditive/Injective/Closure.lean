/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closure Properties of Injective Objects

This leaf packages the finite-product closure supplied by mathlib's
injective-object subcategory as an object-property instance. Consumers can
therefore request the standard closure fact directly rather than reconstruct it
with a local instance.
-/

open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Injective

/-- Stacks 090Y support: injective objects are closed under finite products
whenever those products exist. -/
@[stacks 090Y]
instance closedUnderFiniteProducts :
    (isInjective C).IsClosedUnderFiniteProducts := sorry

#synth (isInjective C).IsClosedUnderFiniteProducts

end Injective

end CategoryTheory
