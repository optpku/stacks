module

public import ReasLib.CategoryTheory.Filtration.AbelianGroups
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v w

/- Exercise 111.3.3: `FilteredObject AddCommGrpCat` is additive and has kernels and cokernels,
and is not the category of filtered k-vector spaces of Exercise 111.3.1 nor the category of
finitely generated torsion-free modules of Exercise 111.3.2. -/
@[stacks 0580]
#check (CategoryTheory.FilteredObject.addCommGrp_not_equivalent_module_categories :
  (∀ (k : Type w) [Field k],
    ¬ Nonempty (FilteredObject AddCommGrpCat.{u} ≌ FilteredObject (ModuleCat.{v} k))) ∧
  (∀ (R : Type w) [CommRing R] [IsDomain R] [IsNoetherianRing R],
    ¬ Nonempty (FilteredObject AddCommGrpCat.{u} ≌ FGTorsionFreeModuleCat.{v} R)))
#check (CategoryTheory.FilteredObject.instPreadditive :
  Preadditive (FilteredObject AddCommGrpCat.{u}))
#check (CategoryTheory.FilteredObject.instHasZeroObject :
  HasZeroObject (FilteredObject AddCommGrpCat.{u}))
#check (CategoryTheory.FilteredObject.instHasBinaryBiproducts :
  HasBinaryBiproducts (FilteredObject AddCommGrpCat.{u}))
#check (CategoryTheory.FilteredObject.hasKernels :
  HasKernels (FilteredObject AddCommGrpCat.{u}))
#check (CategoryTheory.FilteredObject.hasCokernels :
  HasCokernels (FilteredObject AddCommGrpCat.{u}))
