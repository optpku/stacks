/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes over regular rings

This leaf records the module and derived-category characterizations of perfectness over a regular
ring.

@stack 066Z
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-- Lemma 15.75.14 (066Z), module form: over a regular ring, a module is perfect exactly when it
is finite. -/
@[stacks 066Z "perfect modules over a regular ring"]
theorem isPerfect_iff_finite (M : ModuleCat R) :
    M.IsPerfect ↔ Module.Finite R M := sorry

end CategoryTheory.ModuleCat

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-- Lemma 15.75.14 (066Z), derived form: over a regular ring, a derived object is perfect exactly
when it is bounded and all of its homology modules are finite. -/
@[stacks 066Z "perfect derived objects over a regular ring"]
theorem isPerfect_iff_bounded_and_finite_homology
    (K : DerivedCategory (ModuleCat R)) :
    K.IsPerfect ↔
      DerivedCategory.TStructure.t.bounded K ∧
        ∀ i : ℤ, Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) := sorry

end CategoryTheory.DerivedCategory
