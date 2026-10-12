/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Functor.DifferentialGraded
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u u' v v'

variable {C : Type u} {D : Type u'}
variable [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

/- Lemma 22.26.7 (09LB): an additive functor induces a differential graded functor between the
differential graded categories of cochain complexes. -/
@[stacks 09LB] #check
  (CategoryTheory.Functor.mapCochainDg F :
    DgFunctor ℤ (CochainComplex C ℤ) (CochainComplex D ℤ))
#check @CategoryTheory.Functor.mapCochainDg.map
