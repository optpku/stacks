/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Iso

/-!
# Isomorphism cancellation

Isomorphism cancellation is provided by mathlib's `CategoryTheory.Iso.hom_inv_id`,
`CategoryTheory.Iso.inv_hom_id`, and their reassociated simp lemmas. Use
`simp [CategoryTheory.Category.assoc]` for longer composites.
-/
