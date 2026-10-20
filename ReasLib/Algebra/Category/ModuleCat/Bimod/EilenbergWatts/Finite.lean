/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

open CategoryTheory
open Module.Bimodule.RelativeTensor

universe u

namespace ModuleCat
namespace EilenbergWatts

variable {R A B K : Type u}
variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/-- For an admissible functor represented by tensoring with `K`, preservation of
finite right-module objects is equivalent to finite generation of `K` over `B`. -/
theorem mapsFinite_iff
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (hF : Admissible R A B F)
    (hK : Nonempty (F ≅
      (tensorModuleFunctor (R := R) (A := A) (B := B) K :
        ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ))) :
    (∀ M : ModuleCat.{u} Aᵐᵒᵖ,
      Module.Finite Aᵐᵒᵖ M → Module.Finite Bᵐᵒᵖ (F.obj M)) ↔
      Module.Finite Bᵐᵒᵖ K := sorry

end EilenbergWatts
end ModuleCat
