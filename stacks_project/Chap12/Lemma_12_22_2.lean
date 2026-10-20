module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.22.2 [011W]: the category of differential objects in an abelian category is the
one-object specialization of the canonical abelian category of homological complexes. -/
@[stacks 011W]
#check (inferInstance : Abelian (HomologicalComplex C (ComplexShape.refl PUnit.{1})))

end CategoryTheory
