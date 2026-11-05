/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Bounded.Relations
public import ReasLib.CategoryTheory.Filtration.Derived.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Triangulated structure on bounded finite filtered derived categories

The boundedness properties are inverse images of the canonical `t`-structure properties under the
derived associated-graded functor.  Once the exactness instance for that functor is in scope,
Mathlib supplies the canonical `ObjectProperty.inverseImage` and full-subcategory shift and
triangulated instances automatically.  This import-only leaf assembles the required imports.
-/
