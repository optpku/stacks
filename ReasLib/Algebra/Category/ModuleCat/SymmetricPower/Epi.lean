/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphisms and symmetric powers in `ModuleCat`

This leaf records the quotient-preserving part of the symmetric-power functor independently of
the exact sequences that use it.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- Degreewise symmetric powers preserve epimorphisms of modules. -/
@[stacks 00DO "symmetric powers preserve epimorphisms", instance]
instance preservesEpimorphisms (n : ℕ) :
    (functor R n).PreservesEpimorphisms := sorry

/-- A surjective module morphism induces an epimorphism on every symmetric power. -/
@[stacks 00DO "epimorphism on a symmetric power"]
theorem map_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) [Epi f] :
    Epi (map f n) := sorry

end ModuleCat.symmetricPower
