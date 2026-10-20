module

public import ReasLib.Algebra.Category.FGTorsionFreeModuleCat.NonAbelian
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {N M : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M)

/- Exercise 111.3.2 (1): finitely generated torsion-free modules form an additive category. -/
@[stacks 057Z] #check (FGTorsionFreeModuleCat.instHasFiniteBiproducts R :
  HasFiniteBiproducts (FGTorsionFreeModuleCat.{v} R))
#check (CategoryTheory.Preadditive.fullSubcategory (ModuleCat.isFGTorsionFree.{v} R) :
  Preadditive (FGTorsionFreeModuleCat.{v} R))
#check (FGTorsionFreeModuleCat.instContainsZero R :
  (ModuleCat.isFGTorsionFree.{v} R).ContainsZero)
#check (FGTorsionFreeModuleCat.instIsClosedUnderFiniteProducts R :
  (ModuleCat.isFGTorsionFree.{v} R).IsClosedUnderFiniteProducts)

/- Exercise 111.3.2 (2): the kernel is the ordinary module kernel, with its inclusion. -/
@[stacks 057Z] #check (FGTorsionFreeModuleCat.kernelι_isKernel f :
  IsLimit (KernelFork.ofι (FGTorsionFreeModuleCat.kernelι f)
    (FGTorsionFreeModuleCat.kernel_condition f)))
#check (FGTorsionFreeModuleCat.kernelObjIsoKernel f :
  FGTorsionFreeModuleCat.kernelObj f ≅ kernel f)

/- Exercise 111.3.2 (2): the cokernel is the torsion-free quotient of the module cokernel. -/
@[stacks 057Z] #check (FGTorsionFreeModuleCat.cokernelπ_isCokernel f :
  IsColimit (CokernelCofork.ofπ (FGTorsionFreeModuleCat.cokernelπ f)
    (FGTorsionFreeModuleCat.cokernel_condition f)))
#check (FGTorsionFreeModuleCat.cokernelIsoCokernelObj f :
  cokernel f ≅ FGTorsionFreeModuleCat.cokernelObj f)

/- Exercise 111.3.2 (3): multiplication by two on the integer module has a noninvertible
canonical coimage-to-image comparison. -/
@[stacks 057Z] #check (FGTorsionFreeModuleCat.mulTwo_coimageImageComparison_not_isIso :
  ¬ IsIso (Abelian.coimageImageComparison FGTorsionFreeModuleCat.mulTwo))
