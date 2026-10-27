/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.Compatibility

open CategoryTheory AlgebraicGeometry

universe u

variable {p : ℕ} [Fact p.Prime]
variable (B B' : Scheme.Crystalline.Base.{u} p)
variable (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
variable (hbase : g.base ≫ B'.toSpec = B.toSpec)
variable (f : B.source ⟶ B'.source)
variable (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)

/- Remark 60.9.7 (Compatibilities)
The forward crystalline morphism and the base-induced small Zariski morphism commute
with the structure morphisms up to an invertible comparison of ringed topoi. -/
@[stacks 07MH] #check (AlgebraicGeometry.smallCrystallineStructureMorphism_commSq
    B B' g hbase f hf :
  Nonempty (RingedSite.ToposHom.TwoIso
    (X := B.ringedSite)
    (Y := Scheme.AssociatedModule.smallCommRingedSite .zariski B'.scheme)
    (RingedSite.ToposHom.comp
      (X := B.ringedSite) (Y := B'.ringedSite)
      (Z := Scheme.AssociatedModule.smallCommRingedSite .zariski B'.scheme)
      (Scheme.Crystalline.Ringed.morphism B B' g hbase f hf)
      (Scheme.Crystalline.Ringed.structureMorphism B'))
    (RingedSite.ToposHom.comp
      (X := B.ringedSite)
      (Y := Scheme.AssociatedModule.smallCommRingedSite .zariski B.scheme)
      (Z := Scheme.AssociatedModule.smallCommRingedSite .zariski B'.scheme)
      (Scheme.Crystalline.Ringed.structureMorphism B)
      ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom))))
