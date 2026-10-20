/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
import StacksCheckRecall

/-! The reusable first-cohomology API is provided by its mathematical owner. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (cohomology : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : Modules X) (n : ℕ)
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
  AddCommGrpCat.{u})
#check (cohomology_eq : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : Modules X) (n : ℕ)
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
  cohomology X F n =
    (Sheaf.functorH (smallEtaleTopology X) n).obj
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F))
/- Situation 69.16.1: First cohomology vanishes for every quasi-coherent 𝒪_X-module. -/
@[stacks 07UY] #check (AlgebraicGeometry.AlgebraicSpace.HasVanishingH1 :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})], Prop)
#check (HasVanishingH1.of : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
  (∀ (F : Modules X), quasiCoherentModuleProperty X F → IsZero (cohomology X F 1)) →
    HasVanishingH1 X)

end AlgebraicGeometry.AlgebraicSpace
