module

public import stacks_project.Chap111.Exercise_111_3_2_Category
public import stacks_project.Chap111.Exercise_111_3_2_Kernels
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.CategoryTheory.Abelian.Images
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits FGTorsionFreeModuleCat

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {N M : FGTorsionFreeModuleCat.{v} R} (f : N ⟶ M)

/- Exercise 111.3.2 (1): the category of finitely generated torsion-free modules over a
Noetherian domain is additive. -/
@[stacks 057Z] #check (inferInstance : Preadditive (FGTorsionFreeModuleCat.{v} R))
@[stacks 057Z] #check (inferInstance : HasFiniteProducts (FGTorsionFreeModuleCat.{v} R))
@[stacks 057Z] #check (inferInstance : HasFiniteBiproducts (FGTorsionFreeModuleCat.{v} R))

/- Exercise 111.3.2 (2): every morphism in this category has a kernel, given by the ordinary
module kernel. -/
@[stacks 057Z] #check kernelι_isKernel f
@[stacks 057Z] #check kernelObjIsoKernel f

/- Exercise 111.3.2 (3): every morphism in this category has a cokernel, given by the
torsion-free quotient of the module cokernel. -/
@[stacks 057Z] #check cokernelπ_isCokernel f
@[stacks 057Z] #check cokernelIsoCokernelObj f

namespace FGTorsionFreeModuleCat

/-- Multiplication by 2 as an endomorphism of `ℤ` in `FGTorsionFreeModuleCat`. -/
def mulTwo : of ℤ ℤ ⟶ of ℤ ℤ :=
  ofHom (LinearMap.mulLeft ℤ (2 : ℤ))

/-- Exercise 111.3.2 (4): there is a Noetherian domain and a map of finitely generated
torsion-free modules whose canonical coimage-to-image comparison is not an isomorphism. -/
@[stacks 057Z]
theorem mulTwo_coimageImageComparison_not_isIso :
    ¬ IsIso (Abelian.coimageImageComparison mulTwo) :=
  sorry

end FGTorsionFreeModuleCat
