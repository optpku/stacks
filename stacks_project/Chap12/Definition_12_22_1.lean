/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/- Definition 12.22.1 [011V]: differential objects and their morphisms are the canonical
one-object homological complexes and chain maps. -/
@[stacks 011V]
#check HomologicalComplex C (ComplexShape.refl PUnit.{1})

#check @HomologicalComplex.d_comp_d

#check @HomologicalComplex.Hom.comm

end CategoryTheory
