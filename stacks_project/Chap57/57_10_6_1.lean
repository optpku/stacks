/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Functor.Category
import ReasLib.CategoryTheory.NatTrans.Naturality
import StacksCheckRecall

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ C} (c : 𝟭 C ⟶ F)
variable {X X' : C} (f : X ⟶ X')

/- 57.10.6.1: the equation says that the square with component maps c.app X and c.app X'
   commutes along f and F.map f. -/
@[stacks 0FZX] #check (CategoryTheory.NatTrans.naturality_square c f :
  (𝟭 C).map f ≫ c.app X' = c.app X ≫ F.map f)
