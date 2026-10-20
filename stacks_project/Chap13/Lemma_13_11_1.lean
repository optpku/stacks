module

import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Lemma 13.11.1 (`05RS`): the degree-zero homology functor on the homotopy category is
homological.  Both the functor and its homologicality are canonical Mathlib API, so this entry is
a direct recall rather than a chapter-specific wrapper. -/
@[stacks 05RS] #check @HomotopyCategory.homologyFunctor
@[stacks 05RS] #check
  (inferInstance : (HomotopyCategory.homologyFunctor A (up ℤ) 0).IsHomological)
