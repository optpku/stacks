/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphisms and exterior powers in `ModuleCat`

This leaf isolates the quotient-preserving behavior of exterior powers for reuse by exactness,
presentation, and local-property arguments.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Degreewise exterior powers preserve epimorphisms of modules. -/
@[stacks 00DO "exterior powers preserve epimorphisms", instance]
instance preservesEpimorphisms (n : ℕ) :
    (functor R n).PreservesEpimorphisms := sorry

/-- A surjective module morphism induces an epimorphism on every exterior power. -/
@[stacks 00DO "epimorphism on an exterior power"]
theorem map_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) [Epi f] :
    Epi (map f n) := sorry

end ModuleCat.exteriorPower
