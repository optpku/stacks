/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.Construction
public import ReasLib.CategoryTheory.Adjunction.Iteration

/-!
# Generators in the free-forgetful resolution

This leaf owns the iterated free generators and the generator-level formulas for the counit,
comultiplication, faces, and degeneracies. Finite linear-combination formulas are kept in the
separate `Generators.FiniteSums` leaf.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe u

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]

/-- The unit of the free-module adjunction inserts a free generator. -/
@[simp, stacks 0G5T "free-module unit on generators"]
theorem unit.freeMk {X : Type u} (x : X) :
    ((ModuleCat.adj R).unit.app X) x = ModuleCat.freeMk x := sorry

/-- The `(n + 1)`-fold free generator of an element, valued in the corresponding positive
iterate of the free-forgetful endofunctor. The recursion is the generic adjunction-unit
iteration specialized to `ModuleCat.adj`. -/
@[stacks 0G5T "iterated free-module generator"]
noncomputable abbrev freeMk.iterate {R : Type u} [Ring R] (M : ModuleCat R) :
    (n : ℕ) → M → ((functor R) ⁺⦋n⦌).obj M :=
  fun n ↦ CategoryTheory.Adjunction.unit.iterateApp (ModuleCat.adj R) M n

/-- The bundled natural transformation whose components are the iterated free-module generators.
Downstream constructions can use this owner without rebuilding the elementwise recursion. -/
@[stacks 0G5T "bundled iterated free-module generator"]
noncomputable abbrev freeMk.iterateNat (n : ℕ) :=
  CategoryTheory.Adjunction.unit.iterate (ModuleCat.adj R) n

/-- The zeroth positive iterate inserts one free-generator bracket. -/
@[simp, stacks 0G5T "zeroth iterated free-module generator"]
theorem freeMk.iterate_zero {R : Type u} [Ring R] (M : ModuleCat R) (x : M) :
    freeMk.iterate (R := R) M 0 x = ModuleCat.freeMk x := sorry

/-- Passing to the next positive iterate inserts one additional outer free-generator bracket. -/
@[simp, stacks 0G5T "successor iterated free-module generator"]
theorem freeMk.iterate_succ {R : Type u} [Ring R] (M : ModuleCat R) (n : ℕ) (x : M) :
    freeMk.iterate (R := R) M (n + 1) x =
      ModuleCat.freeMk (freeMk.iterate (R := R) M n x) := sorry

/-- The comonad counit evaluates a free generator. -/
@[simp, stacks 0G5T "free-module counit on generators"]
theorem counit.freeMk {R : Type u} [Ring R] (M : ModuleCat R) (x : M) :
    ((counit R).app M) (ModuleCat.freeMk x) = x := sorry

/-- The comonad comultiplication brackets a free generator once more. -/
@[simp, stacks 0G5U "free-module comultiplication on generators"]
theorem comultiplication.freeMk {R : Type u} [Ring R] (M : ModuleCat R) (x : M) :
    ((comultiplication R).app M) (ModuleCat.freeMk x) =
      ModuleCat.freeMk (ModuleCat.freeMk x) := sorry

/-- The zeroth face removes the outer free-generator bracket. -/
@[simp, stacks 0G5U "zeroth face on a free generator"]
theorem face.zero.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) (x : (functor R).obj M) :
    (face R 0 (1 : Fin 2)).app M (ModuleCat.freeMk x) = x := sorry

/-- The first face applies the counit inside the outer free-generator bracket. -/
@[simp, stacks 0G5U "first face on a free generator"]
theorem face.one.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) (x : (functor R).obj M) :
    (face R 0 (0 : Fin 2)).app M (ModuleCat.freeMk x) =
      ModuleCat.freeMk ((counit R).app M x) := sorry

/-- The zeroth degeneracy adds an outer free-generator bracket. -/
@[simp, stacks 0G5U "zeroth degeneracy on a free generator"]
theorem degeneracy.zero.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) (x : (functor R).obj M) :
    (degeneracy R 1 (1 : Fin 2)).app M (ModuleCat.freeMk x) =
      ModuleCat.freeMk (ModuleCat.freeMk x) := sorry

/-- The first degeneracy applies comultiplication inside the outer free-generator bracket. -/
@[simp, stacks 0G5U "first degeneracy on a free generator"]
theorem degeneracy.one.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) (x : (functor R).obj M) :
    (degeneracy R 1 (0 : Fin 2)).app M (ModuleCat.freeMk x) =
      ModuleCat.freeMk ((comultiplication R).app M x) := sorry

end CategoryTheory.ModuleCat.FreeForgetResolution
