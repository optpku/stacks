/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Ring maps to and from products

The graph of an algebra map embeds its source in a product, and the second
projection from a product of commutative rings is flat.
-/

@[expose] public section

universe u

/-- The structure map from an algebra's base ring to its product with that algebra is injective. -/
theorem Algebra.prod_algebraMap_injective (B C : Type u) [CommRing B] [CommRing C]
    [Algebra B C] : Function.Injective (algebraMap B (B × C)) := by
  intro b b' h
  exact congrArg Prod.fst h

/-- The second projection from a product of commutative rings is flat. -/
theorem RingHom.flat_snd (B C : Type u) [CommRing B] [CommRing C] :
    (RingHom.snd B C).Flat := sorry
