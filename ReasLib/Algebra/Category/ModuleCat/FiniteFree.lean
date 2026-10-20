/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite free module categories

This leaf packages finite freeness of bundled modules as an object property and a full
subcategory. It is independent of sheaves and can be reused for stalks, fibers, and derived
cohomology objects.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat

variable (R : Type u) [Ring R]

/-- The object property of a bundled `R`-module being both free and finite. -/
@[stacks 0GT1 "finite-free module property"]
def finiteFree : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Free R M ∧ Module.Finite R M

/-- Finite-free bundled modules are closed under isomorphisms. -/
instance finiteFree.isClosedUnderIsomorphisms :
    (finiteFree.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso := sorry

/-- The full subcategory of finite-free bundled `R`-modules. -/
abbrev FiniteFree := (finiteFree.{u, v} R).FullSubcategory

/-- The underlying module of a bundled finite-free module is free. -/
instance (M : FiniteFree.{u, v} R) : Module.Free R M.obj :=
  M.property.1

/-- The underlying module of a bundled finite-free module is finite. -/
instance (M : FiniteFree.{u, v} R) : Module.Finite R M.obj :=
  M.property.2

/-- Finite-free modules are finite projective. -/
theorem finiteFree_le_finiteProjective :
    finiteFree.{u, v} R ≤ finiteProjective.{u, v} R := sorry

end CategoryTheory.ModuleCat
