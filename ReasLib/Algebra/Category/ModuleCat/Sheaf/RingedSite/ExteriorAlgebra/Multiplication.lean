/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Decomposition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Multiplication.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication formulas under the total exterior decomposition

The direct sheafification construction of exterior-algebra multiplication is compared with the
canonical total exterior monoid.  Homogeneous and degree-one formulas expose the same operation
through the total decomposition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- Under the total decomposition, multiplication on the traditional exterior-algebra sheaf is
the multiplication of the canonical total exterior monoid. -/
@[reassoc (attr := simp), stacks 01CF "exterior multiplication under total decomposition"]
theorem mul_decompositionAppIso_hom (F : ringedSiteModuleCategory J O) :
    mul O F ≫ (decompositionAppIso O F).hom =
      tensorHom (decompositionAppIso O F).hom (decompositionAppIso O F).hom ≫
        μ[((monFunctor O).obj F).X] := sorry

/-- Multiplying homogeneous exterior-power summands in the traditional exterior-algebra sheaf is
fixed-degree exterior multiplication followed by the homogeneous inclusion. -/
@[reassoc, stacks 01CF "homogeneous multiplication in an exterior-algebra sheaf"]
theorem powerι_tensor_powerι_mul
    (F : ringedSiteModuleCategory J O) (n m : ℕ) :
    tensorHom (powerι O F n) (powerι O F m) ≫ mul O F =
      ExteriorPower.mul O F n m ≫ powerι O F (n + m) := sorry

/-- Multiplication of two traditional degree-one generators is degree-`(1 + 1)` exterior
multiplication followed by its homogeneous inclusion. -/
@[reassoc, stacks 01CF "degree-one multiplication in an exterior-algebra sheaf"]
theorem ι_tensor_ι_mul (F : ringedSiteModuleCategory J O) :
    tensorHom (ExteriorAlgebra.ι O F) (ExteriorAlgebra.ι O F) ≫ mul O F =
      tensorHom (ExteriorPower.degreeOne O F) (ExteriorPower.degreeOne O F) ≫
        ExteriorPower.mul O F 1 1 ≫ powerι O F (1 + 1) := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
