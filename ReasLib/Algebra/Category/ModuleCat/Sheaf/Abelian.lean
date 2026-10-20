module

public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O : Sheaf J RingCat.{w}} [UnivLE.{max u v, z}]

/-- Every monomorphism of sheaves of modules over a commutative ring sheaf is normal. -/
theorem isNormalMonoCategoryOfUnivLE :
    IsNormalMonoCategory (SheafOfModules.{z} O) := sorry

/-- Every epimorphism of sheaves of modules over a commutative ring sheaf is normal. -/
theorem isNormalEpiCategoryOfUnivLE :
    IsNormalEpiCategory (SheafOfModules.{z} O) := sorry

/-- Sheaves of modules over a commutative ring sheaf have finite products. -/
theorem hasFiniteProductsOfUnivLE :
    HasFiniteProducts (SheafOfModules.{z} O) := sorry

/-- Sheaves of modules over a commutative ring sheaf have kernels. -/
theorem hasKernelsOfUnivLE :
    HasKernels (SheafOfModules.{z} O) := sorry

/-- Sheaves of modules over a commutative ring sheaf have cokernels. -/
theorem hasCokernelsOfUnivLE :
    HasCokernels (SheafOfModules.{z} O) := sorry

/-- The universe-general abelian structure on sheaves of modules over a commutative ring sheaf. -/
noncomputable instance abelianOfUnivLE :
    Abelian (SheafOfModules.{z} O) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := isNormalMonoCategoryOfUnivLE
  toIsNormalEpiCategory := isNormalEpiCategoryOfUnivLE
  has_finite_products := hasFiniteProductsOfUnivLE
  has_kernels := hasKernelsOfUnivLE
  has_cokernels := hasCokernelsOfUnivLE

end SheafOfModules
