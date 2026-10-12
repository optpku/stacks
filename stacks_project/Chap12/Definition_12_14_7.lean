/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : CochainComplex C ℤ) (k : ℤ)

/- Definition 12.14.7: the shift of a cochain complex is the canonical mathlib shift object
`K⟦k⟧`. -/
@[stacks 011G]
#check (K⟦k⟧ : CochainComplex C ℤ)

/- Mathlib exposes the degree, differential, and map formulas for this owner directly. -/
#check CochainComplex.shiftFunctor_obj_X'
#check CochainComplex.shiftFunctor_obj_d'
#check CochainComplex.shiftFunctor_map_f'
