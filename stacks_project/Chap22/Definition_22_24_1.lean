/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Linear.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

section

variable (R : Type w) [Semiring R]
variable (C : Type u) [Category.{v} C] [Preadditive C]

/- Definition 22.24.1 (09MJ): an `R`-linear category is canonically represented by
`CategoryTheory.Linear R C`. -/
@[stacks 09MJ] #check (CategoryTheory.Linear R C : Type _)

end

section

variable {S : Type w} [CommSemiring S]
variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear S C]
variable (X Y Z : C)

/- Composition in an `S`-linear category is canonically bilinear. -/
#check (CategoryTheory.Linear.comp (S := S) X Y Z :
  (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z)

end
