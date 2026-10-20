/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable (A : Sheaf J CommRingCat.{u}) (B : Under A)

/- Equation 18.35.0.2 (08TV): the differential of the canonical naive cotangent complex is the
conormal morphism of the canonical polynomial presentation. -/
@[stacks 08TV]
#check (NaiveCotangent.d_negOne_zero A B :
  (NaiveCotangent.obj A B).d (-1) 0 =
    conormalMap (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B))

/- Exactness of the canonical conormal sequence identifies the cokernel with `Ω(B/A)`. -/
#check NaiveCotangent.Presentation.conormalSequence_exact A B
