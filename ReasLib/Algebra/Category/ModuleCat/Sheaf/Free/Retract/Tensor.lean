module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract.FiniteCoproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit

/-!
# Tensor products of finite-free retract module sheaves

For the canonical tensor product on modules over a commutative ring sheaf, finite-free retracts
are closed under tensor products.  The result is stated as an `ObjectProperty.TensorLE` instance
so downstream complex-level arguments can use the generic termwise tensor API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose
  (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {O : Sheaf J CommRingCat.{w}}

/-- Finite-free retract module sheaves are closed under the canonical tensor product. -/
@[stacks 09J2 "finite-free retract tensor closure"]
instance finiteFreeRetractModuleProperty_tensorLE :
    ObjectProperty.TensorLE
      (SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O))
      (SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O))
      (SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O)) := sorry

namespace finiteFreeRetractModuleProperty

/-- The tensor product of two finite-free retract module sheaves is a finite-free retract. -/
theorem tensor
    {M N : ringedSiteModuleCategory.{u, v, w, w} J O}
    (hM : SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) M)
    (hN : SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) N) :
    SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O)
      (((CategoryTheory.MonoidalCategory.curriedTensor
        (ringedSiteModuleCategory.{u, v, w, w} J O)).obj M).obj N) := sorry

end finiteFreeRetractModuleProperty

end SheafOfModules.RingedSite
