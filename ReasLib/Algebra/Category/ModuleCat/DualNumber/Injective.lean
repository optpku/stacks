/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Residue

@[expose] public section

/-!
# Self-injectivity of the dual numbers

@stack 0A5U

The field hypothesis is isolated here so that residue-module and periodic-complex consumers do
not acquire it through the foundational imports.
-/

universe u

open CategoryTheory

namespace DualNumber

variable (k : Type u) [Field k]

/-- The regular module over the dual numbers of a field is injective. -/
@[stacks 0A5U "dual numbers are self-injective"]
instance regularInjective :
    Module.Injective (DualNumber k) (DualNumber k) := sorry

/-- The regular dual-number module is an injective object of its module category. -/
@[stacks 0A5U "categorical self-injectivity of the dual numbers"]
instance regularInjectiveObject :
    Injective (ModuleCat.of (DualNumber k) (DualNumber k)) := sorry

#synth Module.Injective (DualNumber k) (DualNumber k)
#synth Injective (ModuleCat.of (DualNumber k) (DualNumber k))

end DualNumber
