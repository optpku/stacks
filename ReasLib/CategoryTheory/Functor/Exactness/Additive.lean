module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of exact functors

This module records the additive structure forced by finite-limit or
finite-colimit preservation between abelian categories.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B)

/-- A left exact or right exact functor between abelian categories is additive. -/
@[stacks 010N]
theorem additive_of_leftExact_or_rightExact
    (hF : leftExactFunctor A B F ∨ rightExactFunctor A B F) : F.Additive := sorry

end CategoryTheory.Functor

namespace CategoryTheory.ExactFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- A bundled exact functor between abelian categories carries its canonical
additive structure. -/
@[stacks 010N "bundled exact functors are additive"]
noncomputable instance additive (F : A ⥤ₑ B) : F.obj.Additive :=
  ((AdditiveFunctor.ofExact A B).obj F).property

end CategoryTheory.ExactFunctor
