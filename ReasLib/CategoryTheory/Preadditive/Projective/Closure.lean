/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closure properties of projective objects

This file owns closure facts intrinsic to projective objects.  Keeping these instances at the
projective-object layer lets complexes and resolutions reuse them without rebuilding local
transport instances.
@stack 0A5N
-/

@[expose] public section

universe v u

namespace CategoryTheory.Projective

variable {C : Type u} [Category.{v} C]

/-- Projective objects are stable under isomorphism. -/
@[stacks 0A5N "projective objects are invariant under isomorphism"]
instance closedUnderIsomorphisms :
    (isProjective C).IsClosedUnderIsomorphisms := sorry

#synth (isProjective C).IsClosedUnderIsomorphisms

end CategoryTheory.Projective
