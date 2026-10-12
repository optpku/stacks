/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Representable
import StacksCheckRecall

/-!
# Lemma 22.26.10

The endomorphism DGA and representable right-module functor are owned at the level of an
arbitrary differential graded category by
`ReasLib.Algebra.Category.DifferentialGraded.Representable`.
-/

@[expose] public section

universe u v w

open CategoryTheory

variable {R : Type u} [CommRing R]
variable {C : Type v} [DifferentialGradedCategory.{u, v, w} R C]
variable (x : C)

/- Lemma 22.26.10 (09LE): every object of a differential graded category has a canonical
endomorphism DGA. -/
@[stacks 09LE]
#check
  (DifferentialGradedCategory.endomorphismDGA x : CochainDGAlgebra.{u, w} R)

/- The represented homogeneous hom object is a right module over the endomorphism DGA by
precomposition. -/
#check @DifferentialGradedCategory.representableModule

/- The right action is homogeneous precomposition, including the canonical degree transport. -/
#check @DifferentialGradedCategory.representableModule_smul

/- Closed degree-zero postcomposition makes the represented modules functorial in the target. -/
#check @DifferentialGradedCategory.representableFunctor

/- The functor acts on morphisms by homogeneous postcomposition. -/
#check @DifferentialGradedCategory.representableMap_apply
