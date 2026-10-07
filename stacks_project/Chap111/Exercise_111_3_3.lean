module

public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.CategoryTheory.Filtration.Preabelian
public import ReasLib.CategoryTheory.Filtration.Preadditive
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Limits

universe u

/- Exercise 111.3.3: `FilteredObject AddCommGrpCat` is additive and has kernels and cokernels,
and is not the category of filtered k-vector spaces of Exercise 111.3.1 nor the category of
finitely generated torsion-free modules of Exercise 111.3.2. -/
@[stacks 0580]
#check (inferInstance : Preadditive (FilteredObject AddCommGrpCat.{u}))
@[stacks 0580]
#check (inferInstance : HasZeroObject (FilteredObject AddCommGrpCat.{u}))
@[stacks 0580]
#check (inferInstance : HasBinaryBiproducts (FilteredObject AddCommGrpCat.{u}))
@[stacks 0580]
#check (inferInstance : HasKernels (FilteredObject AddCommGrpCat.{u}))
@[stacks 0580]
#check (inferInstance : HasCokernels (FilteredObject AddCommGrpCat.{u}))
