/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Biproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Linear

/-!
# Binary biproducts of module sheaves over an algebra sheaf

The module-sheaf category is preadditive, so its canonical binary coproducts determine binary
biproducts.  This owner is kept below homotopy and triangulated constructions so those layers do
not have to install a competing local instance.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Binary biproducts of module sheaves over a commutative algebra sheaf. -/
@[stacks 09LV "binary biproducts for algebra-sheaf modules", instance]
noncomputable instance modulesHasBinaryBiproducts :
    HasBinaryBiproducts
      (Modules.{r, u, v, w, max u z} O) :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

end SheafOfModules.CommAlg
