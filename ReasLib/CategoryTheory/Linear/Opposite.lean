module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear structure on opposite categories

The opposite of an `R`-linear category is canonically `R`-linear.  Only this forward construction
is an instance; registering a converse construction would create a typeclass-search cycle.
-/

@[expose] public section

noncomputable section

universe w v u

open Opposite

namespace CategoryTheory

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The opposite of an `R`-linear category has the transported `R`-linear structure. -/
@[stacks 09MJ "linear opposite category"]
instance instLinearOpposite : Linear R Cᵒᵖ where
  homModule X Y := Equiv.module R (opEquiv X Y)
  smul_comp := sorry
  comp_smul := sorry

/-- Taking the underlying arrow of an opposite morphism commutes with scalar multiplication. -/
@[stacks 09MJ "scalar multiplication on opposite morphisms", simp]
theorem unop_smul {X Y : Cᵒᵖ} (r : R) (f : X ⟶ Y) :
    (r • f).unop = r • f.unop := sorry

/-- Taking the opposite of a morphism commutes with scalar multiplication. -/
@[stacks 09MJ "scalar multiplication on reversed morphisms", simp]
theorem op_smul {X Y : C} (r : R) (f : X ⟶ Y) :
    (r • f).op = r • f.op := sorry

end CategoryTheory

end
