module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.Defs
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import ReasLib.CategoryTheory.Filtration.KernelCokernel.Universal
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Basic
public import ReasLib.CategoryTheory.Filtration.VectorSpaceCounterexample
public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace CategoryTheory

section
variable {k : Type u} [Field k]
variable {V W : FilteredObject (ModuleCat.{u} k)} (f : V ⟶ W)

/- Exercise 111.3.1 (1): the category of filtered k-vector spaces is additive. -/
@[stacks 057Y]
#check (CategoryTheory.FilteredObject.instPreadditive : Preadditive (FilteredObject (ModuleCat.{u} k)))
#check (CategoryTheory.FilteredObject.instHasZeroObject : HasZeroObject (FilteredObject (ModuleCat.{u} k)))
#check (CategoryTheory.FilteredObject.instHasBinaryBiproducts : HasBinaryBiproducts (FilteredObject (ModuleCat.{u} k)))

/- Exercise 111.3.1 (1): the direct sum has the ambient direct sum as its underlying object,
with the biproduct of the two stage inclusions giving its decreasing filtration. -/
@[stacks 057Y]
#check (CategoryTheory.FilteredObject.binaryBiproduct V W : FilteredObject (ModuleCat.{u} k))
#check (CategoryTheory.FilteredObject.binaryBiproduct_obj V W :
  (CategoryTheory.FilteredObject.binaryBiproduct V W).obj = (V.obj ⊞ W.obj))
#check (CategoryTheory.FilteredObject.binaryBiproduct_filtration V W :
  (CategoryTheory.FilteredObject.binaryBiproduct V W).filtration =
    CategoryTheory.DecreasingFiltration.biprod V.filtration W.filtration)

/- Exercise 111.3.1 (2): a morphism of filtered k-vector spaces has a kernel and cokernel, given
by the underlying kernel with induced filtration and underlying cokernel with quotient filtration.
-/
@[stacks 057Y]
#check (CategoryTheory.FilteredObject.Hom.kernel f : FilteredObject (ModuleCat.{u} k))
#check (CategoryTheory.FilteredObject.Hom.kernelιIsLimit f :
  IsLimit (KernelFork.ofι (FilteredObject.Hom.kernelι f) (FilteredObject.Hom.kernelι_comp f)))
#check (CategoryTheory.FilteredObject.Hom.cokernel f : FilteredObject (ModuleCat.{u} k))
#check (CategoryTheory.FilteredObject.Hom.toCokernelIsColimit f :
  IsColimit (CokernelCofork.ofπ (FilteredObject.Hom.toCokernel f)
    (FilteredObject.Hom.comp_toCokernel f)))

end

section
variable {k : Type u} [Field k]

/- Exercise 111.3.1 (3): an identity between adjacent jump filtrations has a non-isomorphic
coimage-image comparison. -/
@[stacks 057Y]
#check (CategoryTheory.FilteredObject.not_isIso_coimageImageComparison_lineId (k := k) :
  ¬ IsIso (CategoryTheory.FilteredObject.Hom.coimageImageComparison (CategoryTheory.FilteredObject.lineId k)))

end

end CategoryTheory

end
