module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {A B A' B' : Sheaf J CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
variable (sq : CommSq ρ α β φ)

/- 92.18.2.1: a commutative square of sheaves of rings on a site C,
with vertices A, B, A', B' and arrows α : A ⟶ B, ρ : A ⟶ A',
β : A' ⟶ B', φ : B ⟶ B'. -/
@[stacks 08ST] #check (sq : CommSq ρ α β φ)

#check (sq.w : ρ ≫ β = α ≫ φ)
