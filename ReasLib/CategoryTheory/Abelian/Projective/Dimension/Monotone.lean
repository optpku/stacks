/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monotonicity of projective-dimension bounds

`HasProjectiveDimensionLE X n` is an upper-bound predicate.  Mathlib exposes the underlying
strict bound as a typeclass, while applications often have an explicit proof term.  This leaf
supplies the explicit monotonicity interface, so consumers do not need a temporary local instance
solely to weaken a bound.
-/

@[expose] public section

universe u v

namespace CategoryTheory.HasProjectiveDimensionLE

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A projective-dimension bound can be relaxed along an inequality. -/
@[stacks 00O5 "monotonicity of projective-dimension bounds"]
theorem of_le {X : C} {m n : ℕ}
    (hX : HasProjectiveDimensionLE X m) (hmn : m ≤ n) :
    HasProjectiveDimensionLE X n := sorry

/-- A projective-dimension bound can be relaxed by one. -/
@[stacks 00O5 "successor projective-dimension bound"]
abbrev succ {X : C} {n : ℕ} (hX : HasProjectiveDimensionLE X n) :
    HasProjectiveDimensionLE X (n + 1) :=
  of_le hX (Nat.le_succ _)

end CategoryTheory.HasProjectiveDimensionLE
