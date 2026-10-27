/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.BigRinged
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Crystalline.Ringed

variable {p : ℕ} [Fact p.Prime]

/-- The structure morphism from the small crystalline ringed topos to the big Zariski
ringed topos of the divided-power base sends each thickening to its scheme over the base. -/
def bigZariskiStructureMorphism (B : Base.{u} p) :
    RingedSite.ToposHom B.ringedSite
      (Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme) :=
  RingedSite.ToposHom.comp
    (X := B.ringedSite) (Y := B.bigRingedSite)
    (Z := Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme) (smallToBig B)
    (@RingedSite.Cocontinuous.toRingedTopos B.bigRingedSite
      (Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme)
      B.bigThickeningOverBase (bigThickeningOverBase_isCocontinuous B)
      inferInstance inferInstance inferInstance inferInstance (baseStructureMap B))

end Scheme.Crystalline.Ringed

/-- A compatible morphism of prime-local divided-power bases and source schemes commutes
with the crystalline structure morphisms to the small Zariski ringed topoi up to an
invertible comparison compatible with the structure-ring maps. -/
theorem smallCrystallineStructureMorphism_commSq
    {p : ℕ} [Fact p.Prime] (B B' : Scheme.Crystalline.Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec) (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
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
        ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom))) := sorry

end AlgebraicGeometry
