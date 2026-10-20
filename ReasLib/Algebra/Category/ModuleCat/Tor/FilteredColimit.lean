/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor and Filtered Colimits

Fixing the right argument of the module `Tor` bifunctor gives a functor preserving
filtered colimits.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- Tag 0BNF: for a fixed module `N`, the functor `Torₙ(-, N)` preserves filtered colimits
of the specified size. -/
@[stacks 0BNF]
instance preservesFilteredColimitsOfSize (N : ModuleCat.{u} R) (n : ℕ) :
    PreservesFilteredColimitsOfSize.{v, v}
      ((CategoryTheory.Tor (ModuleCat.{u} R) n).flip.obj N) := sorry

end CategoryTheory.ModuleCat.Tor
