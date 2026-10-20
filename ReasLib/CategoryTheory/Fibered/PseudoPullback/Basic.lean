/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Computations
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Naturality

/-!
# Explicit pseudo-pullbacks of categories over a base

This is the compatibility import for the foundational explicit pseudo-pullback API in `Cat/C`.
The implementation is organized by responsibility:

* `Basic.Construction` owns the private carrier, category structure, constructor, and structural
  accessors;
* `Basic.Computations` owns the object and morphism projection formulas;
* `Basic.Naturality` owns base-transport naturality, comparison compatibility, and public eta/ext
  principles.

New developments should import the smallest leaf matching their need. This aggregate remains the
stable entry point for existing imports of `Fibered.PseudoPullback.Basic`.
-/
