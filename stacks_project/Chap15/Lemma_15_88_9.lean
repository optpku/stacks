module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Tensor
import StacksCheckRecall

/-!
@stack 091H

Lemma 15.88.9 is the canonical derived tensor product on modules over a sequential varying-ring
system.  Its construction uses stagewise K-flat representatives; the shared `DerivedTensor` API
owns the tensor, symmetry, and triangulated exactness.
-/

@[expose] public section

open CategoryTheory ComplexShape

/- Lemma 15.88.9 (1): the unbounded derived tensor product exists. -/
@[stacks 091H "(1)"]
#check @CategoryTheory.SequentialInverseSystem.ModuleSystem.hasDerivedTensor

/- Lemma 15.88.9 (2): evaluation at every stage is compatible with derived tensor product. -/
@[stacks 091H "(2)"]
#check @CategoryTheory.SequentialInverseSystem.ModuleSystem.derivedEvaluationTensor_isomorphic

/- Lemma 15.88.9 (3): the derived tensor product is symmetric. -/
@[stacks 091H "(3)"]
#check @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Right.comm

/- Lemma 15.88.9 (4): fixing either tensor factor gives a triangulated functor. -/
@[stacks 091H "(4), fixed right factor"]
#check @CategoryTheory.SequentialInverseSystem.ModuleSystem.derivedTensorRight_isTriangulated

@[stacks 091H "(4), fixed left factor"]
#check @CategoryTheory.SequentialInverseSystem.ModuleSystem.derivedTensorLeft_isTriangulated
