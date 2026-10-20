/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Tensor
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor

@[expose] public section

universe u

namespace CharacterModule

/-- The character module of a flat module over a commutative ring is injective. -/
@[instance]
theorem injective_of_flat (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    [Module.Flat R M] : Module.Injective R (moduleObj R M) := sorry

end CharacterModule
