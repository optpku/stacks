/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Square.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of bounded replacement squares

The two-sided bounded replacement is the composite of the upper and lower truncation functors, so
its additive transport is exposed as a separate small support leaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.Replace.Square.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The bounded replacement functor at fixed bounds preserves addition. -/
@[stacks 05S5 "additivity of bounded filtered replacement"]
noncomputable instance functor_additive (a b : ℤ) :
    (functor (A := A) a b).Additive := sorry

#synth (functor (A := A) 0 0).Additive

end CategoryTheory.FilteredComplex.Replace.Square.Bounded
