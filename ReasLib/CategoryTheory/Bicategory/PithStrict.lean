/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strictness of the pith

Taking the homwise core of a strict bicategory preserves strictness.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory.Pith

variable {B : Type u} [Bicategory.{w, v} B] [Strict B]

/-- The pith of a strict bicategory is strict. -/
@[stacks 003K "strictness of the pith"]
instance strict : Strict (Pith B) := sorry
/- Proof strategy: obtain the identity and associativity equalities by applying `congrArg Core.mk`
to the corresponding `Strict B` fields. Rewrite the ambient unitors and associator with
`Strict.leftUnitor_eqToIso`, `Strict.rightUnitor_eqToIso`, and
`Strict.associator_eqToIso`; after each rewrite, cases on the relevant equality identifies
`Core.isoMk (eqToIso e)` with `eqToIso (congrArg Core.mk e)`. -/

end Bicategory.Pith

end CategoryTheory
