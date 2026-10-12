/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of constant-diagram functors

The constant-diagram functor into a functor category is additive whenever the
coefficient category is preadditive.  This is independent of the shape of the
diagram and is useful before passing to derived categories.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Functor

variable {J : Type v} [Category J]
variable {C : Type u} [Category C] [Preadditive C]

/-- The constant-diagram functor into `J ⥤ C` is additive. -/
instance constant_additive :
    (Functor.const J : C ⥤ J ⥤ C).Additive := ⟨rfl⟩

end CategoryTheory.Functor
