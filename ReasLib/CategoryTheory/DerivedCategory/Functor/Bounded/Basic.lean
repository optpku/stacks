/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Basic

/-!
# Functors from bounded homotopy categories to derived categories

This compatibility facade exports the bounded-below, bounded-above, and two-sided bounded induced
functors and their basic computation and triangulated API. Import a directional `Basic` leaf when
only one boundedness direction is required.
-/
