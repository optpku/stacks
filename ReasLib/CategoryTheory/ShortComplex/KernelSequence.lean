/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel Sequences of Epimorphisms

This leaf extends the abelian `ShortComplex.kernelSequence` API to a preadditive
category in which epimorphisms are normal.  It deliberately exposes only the
short-exactness statement: the kernel and the two maps are already owned by
mathlib's `Limits.kernel` construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C]
  [HasZeroObject C] [IsNormalEpiCategory C]

/-- A kernel followed by an epimorphism is a short exact sequence in a preadditive category
whose epimorphisms are normal. -/
@[stacks 00O3 "kernel sequence of an epimorphism"]
theorem kernelSequence_shortExact_of_epi {X Y : C} (q : X ⟶ Y) [Epi q] :
    (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact := sorry

end CategoryTheory.ShortComplex
