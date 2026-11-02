/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import ReasLib.CategoryTheory.Functor.Objwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise properties of simplicial sets

This file connects the standard finiteness and nonemptiness notions for simplicial sets to the
generic objectwise functor properties used by indexed limits and colimits.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

/-- A simplicial set with a vertex has a simplex in every simplicial degree. This is the named
term-level form of mathlib's degreewise nonemptiness instance. -/
@[stacks 017I "degreewise nonemptiness from a vertex"]
theorem Nonempty.obj (U : SSet.{u}) [U.Nonempty]
    (Delta : SimplexCategoryᵒᵖ) : _root_.Nonempty (U.obj Delta) := inferInstance

namespace Finite

/-- A finite simplicial set is objectwise finite. -/
@[stacks 017E "finite simplicial sets are objectwise finite"]
instance (priority := 100) objFinite (U : SSet.{u}) [U.Finite] : U.ObjFinite :=
  ⟨fun _ ↦ inferInstance⟩

end Finite

namespace ObjFinite

/-- The tensor product of objectwise finite simplicial sets is objectwise finite. -/
@[stacks 017I "objectwise finite simplicial-set tensor"]
instance tensor (U V : SSet.{u}) [U.ObjFinite] [V.ObjFinite] : (U ⊗ V).ObjFinite :=
  ⟨fun _ ↦ inferInstance⟩

end ObjFinite

namespace Nonempty

/-- A simplicial set with a vertex is objectwise nonempty. This is a theorem rather than an
instance to avoid a cycle with evaluation of `Functor.ObjNonempty` in degree zero. -/
@[stacks 017E "nonempty simplicial sets are objectwise nonempty"]
theorem objNonempty (U : SSet.{u}) [U.Nonempty] : U.ObjNonempty :=
  ⟨fun Delta ↦ SSet.Nonempty.obj U Delta⟩

/-- The tensor product of nonempty simplicial sets is nonempty. -/
@[stacks 017I "nonempty simplicial-set tensor"]
instance tensor (U V : SSet.{u}) [U.Nonempty] [V.Nonempty] : (U ⊗ V).Nonempty :=
  inferInstanceAs (_root_.Nonempty (U _⦋0⦌ × V _⦋0⦌))

end Nonempty

end SSet
