/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Colimits of Type-valued sheaves

Mathlib's generic `Sheaf` colimit instance already derives all colimits of
`Type`-valued sheaves from the coefficient category.  This compatibility
import deliberately adds no project instance: downstream code should use the
canonical Mathlib instance and avoid typeclass overlap.
-/
