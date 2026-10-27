/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Restriction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

@[expose] public section

universe u

namespace CrystallineModuleSheaf

variable (p : ℕ) [Fact p.Prime] (B : Base.{u} p)
  (F : SheafOfModules (structureSheaf (S := B.scheme) (I := B.ideal)
    (γ := B.dividedPowers) (h_compatible := B.compatible)
    (X := B.source) (x₀ := B.sourceToClosed)))
  (G : SheafOfModules (smallStructureSheaf (S := B.scheme) (I := B.ideal)
    (γ := B.dividedPowers) (h_compatible := B.compatible)
    (X := B.source) (x₀ := B.sourceToClosed)))

/- Definition 60.11.1: local quasi-coherence means quasi-coherence of the
actual restriction to every thickening in the big crystalline site. -/
@[stacks 07IS] #check
  (CrystallineModuleSheaf.ModuleSheaf.isLocallyQuasiCoherent_iff
    (CrystallineModuleSheaf.restrict F) :
    ModuleSheaf.IsLocallyQuasiCoherent (CrystallineModuleSheaf.restrict F) ↔
      ∀ A : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed, (CrystallineModuleSheaf.restrictObj F A).IsQuasicoherent)

/- On the small crystalline site, local quasi-coherence has the same
objectwise meaning. -/
#check
  (CrystallineModuleSheaf.CrisModuleSheaf.isLocallyQuasiCoherent_iff
    (CrystallineModuleSheaf.CrisModuleSheaf.restrict G) :
    CrisModuleSheaf.IsLocallyQuasiCoherent (CrisModuleSheaf.restrict G) ↔
      ∀ A : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed, (CrisModuleSheaf.restrictObj G A).IsQuasicoherent)

/- A crystal on the big crystalline site has invertible comparison maps
for every morphism. -/
#check
  (CrystallineModuleSheaf.ModuleSheaf.isCrystal_iff (CrystallineModuleSheaf.restrict F) :
    ModuleSheaf.IsCrystal (CrystallineModuleSheaf.restrict F) ↔
      ∀ {A A' : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed} (f : A ⟶ A'),
          IsIso (CrystallineModuleSheaf.restrictComparison F f))

/- The crystal condition on the small crystalline site uses its actual
restriction comparison maps. -/
#check
  (CrystallineModuleSheaf.CrisModuleSheaf.isCrystal_iff (CrisModuleSheaf.restrict G) :
    CrisModuleSheaf.IsCrystal (CrisModuleSheaf.restrict G) ↔
      ∀ {A A' : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed} (f : A ⟶ A'),
          IsIso (CrisModuleSheaf.restrictComparison G f))

section BigQuasiCoherence

variable
  [∀ A : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed,
    HasWeakSheafify
      ((crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed).over A) AddCommGrpCat.{u}]
  [∀ A : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed,
    ((crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed).over A).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Quasi-coherence on the big site is the canonical Modules on Sites notion. -/
#check (SheafOfModules.IsQuasicoherent F : Prop)

end BigQuasiCoherence

section SmallQuasiCoherence

variable
  [∀ A : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed,
    HasWeakSheafify
      ((smallCrystallineZariskiTopology (S := B.scheme) (I := B.ideal)
        (γ := B.dividedPowers) (h_compatible := B.compatible)
        (X := B.source) (x₀ := B.sourceToClosed)).over A) AddCommGrpCat.{u}]
  [∀ A : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed,
    ((smallCrystallineZariskiTopology (S := B.scheme) (I := B.ideal)
      (γ := B.dividedPowers) (h_compatible := B.compatible)
      (X := B.source) (x₀ := B.sourceToClosed)).over A).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Quasi-coherence on the small site is the same canonical notion. -/
#check (SheafOfModules.IsQuasicoherent G : Prop)

end SmallQuasiCoherence

end CrystallineModuleSheaf

end
