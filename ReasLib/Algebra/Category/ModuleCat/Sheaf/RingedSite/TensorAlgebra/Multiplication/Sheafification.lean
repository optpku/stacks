/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorAlgebra.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unit and multiplication on tensor-algebra sheaves

The sectionwise unit and multiplication are transported through the strong monoidal
sheafification functor.  This gives concrete algebra operations on the traditional
sheafification model of the tensor algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.TensorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The multiplicative unit of the tensor-algebra sheaf. -/
@[stacks 01CF "unit of a tensor-algebra sheaf"]
noncomputable def one (F : ringedSiteModuleCategory J O) :
    𝟙_ (ringedSiteModuleCategory J O) ⟶ sheaf O F :=
  Functor.LaxMonoidal.ε (moduleSheafification O) ≫
    (moduleSheafification O).map
      (PresheafOfModules.TensorAlgebra.oneHom O.obj F.val)

/-- Multiplication on the tensor-algebra sheaf. -/
@[stacks 01CF "multiplication on a tensor-algebra sheaf"]
noncomputable def mul (F : ringedSiteModuleCategory J O) :
    tensorObj (sheaf O F) (sheaf O F) ⟶ sheaf O F :=
  (ModuleSheafification.tensorIso O (presheaf O F) (presheaf O F)).hom ≫
    (moduleSheafification O).map
      (PresheafOfModules.TensorAlgebra.mulHom O.obj F.val)

/-- Tensor-algebra sheaf units are natural in the module sheaf. -/
@[reassoc, stacks 01CF "naturality of tensor-algebra sheaf units"]
theorem one_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    one O F ≫ map O f = one O G := sorry

/-- Tensor-algebra sheaf multiplication is natural in the module sheaf. -/
@[reassoc, stacks 01CF "naturality of tensor-algebra sheaf multiplication"]
theorem mul_naturality {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    tensorHom (map O f) (map O f) ≫ mul O G = mul O F ≫ map O f := sorry

end SheafOfModules.RingedSite.TensorAlgebra
