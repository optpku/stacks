/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Gorenstein.InjectiveDimension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.RegularModule

@[expose] public section

open CategoryTheory

universe u

/- Lemma [Stacks 0HB2] (1): a Noetherian commutative ring A has finite injective
dimension as a module over itself if and only if A is Gorenstein and of finite Krull
dimension. -/
@[stacks 0HB2] #check
  (IsGorensteinRing.injectiveDimension_self_ne_top_iff :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
      injectiveDimension (ModuleCat.of A A) ≠ ⊤ ↔
        IsGorensteinRing A ∧ ringKrullDim A ≠ ⊤)

/- Lemma [Stacks 0HB2] (2): in this case the regular module concentrated in degree
zero is a dualizing complex. -/
@[stacks 0HB2] #check
  (CategoryTheory.DerivedCategory.IsDualizing.ringSingle_of_injectiveDimension_self_ne_top :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
      injectiveDimension (ModuleCat.of A A) ≠ ⊤ →
        CategoryTheory.DerivedCategory.IsDualizing (ModuleCat.single0 (ModuleCat.of A A)))
