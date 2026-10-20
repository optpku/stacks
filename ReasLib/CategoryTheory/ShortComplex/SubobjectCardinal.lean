/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Subobject.Cardinal

@[expose] public section

/-!
# Subobject Cardinals in Short Exact Sequences

The two cardinal inequalities for a short exact sequence are exposed as specializations of the
subobject-lattice comparison API for monomorphisms and epimorphisms.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C]

section Mono

variable [HasZeroMorphisms C] {S : ShortComplex C}

/-- Lemma 19.11.3 (1): the first object of a short exact sequence has no more subobjects than the
middle object. -/
@[stacks 079D "(1)"]
theorem subobjectCardinal_f_le (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₁) ≤ Cardinal.mk (Subobject S.X₂) := sorry

end Mono

section Abelian

variable [Abelian C] {S : ShortComplex C}

/-- Lemma 19.11.3 (2): the third object of a short exact sequence has no more subobjects than the
middle object. -/
@[stacks 079D "(2)"]
theorem subobjectCardinal_g_le (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₃) ≤ Cardinal.mk (Subobject S.X₂) := sorry

end Abelian

end CategoryTheory.ShortComplex.ShortExact
