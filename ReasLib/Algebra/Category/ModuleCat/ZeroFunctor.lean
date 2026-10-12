/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Zero
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Functors on Module Categories

The concrete nonzero module that turns the category-theoretic zero-functor criteria into the
`ModuleCat (ZMod 2)` counterexample.
-/

@[expose] public section

open CategoryTheory.Limits

namespace ModuleCat.ZeroFunctor

/-- Remark 12.29.4 (2) [03B9]: the regular `ZMod 2`-module is not a zero object. -/
@[stacks 03B9 "(2)"]
theorem zModTwo_regular_not_isZero :
    ¬ IsZero (ModuleCat.of (ZMod 2) (ZMod 2)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_subsingleton_iff_nontrivial.mpr inferInstance

end ModuleCat.ZeroFunctor
