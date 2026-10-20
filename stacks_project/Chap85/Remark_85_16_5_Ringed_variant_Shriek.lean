/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Module

/-!
# Module lower shriek for simplicial total localization

Specialized names for total lower shriek and operator exactness remain available
for source consumers of the simplicial localization interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w z

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))

/-- The functor `a_! : Mod(O) ⥤ Mod(O_C)`, module lower shriek along `totalForget`.
It is left adjoint to restriction and is not generally exact. -/
abbrev moduleLowerShriek :
    SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} X.structureSheaf :=
  Cocontinuous.moduleLowerShriek (totalForget K) X.structureSheaf

/-- The adjunction `a_! ⊣ a^*` of module lower shriek along `totalForget` with module
inverse image. -/
abbrev moduleLowerShriek_adjunction :
    (moduleLowerShriek K :
      SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} X.structureSheaf) ⊣
      Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf :=
  Cocontinuous.moduleLowerShriek.adjunction (totalForget K) X.structureSheaf

end RingedSite.Localization.AtSimplicialSR
