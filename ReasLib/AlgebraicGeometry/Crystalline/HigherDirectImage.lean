/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Evaluation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Evaluation

/-- Restriction of a crystalline module to a thickening is localization at the
crystalline object followed by evaluation on the thickening's small Zariski site. -/
def moduleRestriction {p : ℕ} [Fact p.Prime] (B : Base.{u} p) (A : B.ringedSite) :
    RingedSite.ModuleCat.{u + 1} B.ringedSite ⥤
      RingedSite.ModuleCat.{u + 1}
        (Scheme.AssociatedModule.smallCommRingedSite .zariski A.obj.1.thickening) :=
  RingedSite.Hom.localizedRestriction B.ringedSite A ⋙
    (evaluation B A).modulePushforward

end AlgebraicGeometry.Scheme.Crystalline.Evaluation

/-- A compatible divided-power base map and source square induce higher direct
images of quasi-coherent crystals that are quasi-coherent on every target
thickening, provided the base map and source-to-closed-fibre map are quasi-compact
and quasi-separated. -/
theorem crystallineHigherDirectImage_isLocallyQuasiCoherent
    {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    [QuasiCompact g.base] [QuasiSeparated g.base]
    [QuasiCompact B.sourceToClosed] [QuasiSeparated B.sourceToClosed]
    (F : RingedSite.ModuleCat.{u + 1} B.ringedSite)
    [IsCrystalInQuasiCoherentModules F] (i : ℕ) :
    ∀ A' : B'.ringedSite,
      ((Evaluation.moduleRestriction B' A').obj
        (RingedSite.ToposHom.higherDirectImageModule.{u + 1, u, u + 1, u, u + 1}
          (Ringed.morphism B B' g hbase f hf) F i)).IsQuasicoherent :=
  sorry

/-- For a compatible divided-power base map and source square, a quasi-compact
and quasi-separated base map and a finite type, quasi-separated source-to-closed-fibre
map give a uniform bound above which all higher direct images of quasi-coherent
crystals vanish. -/
theorem crystallineHigherDirectImage_eventually_isZero
    {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    [QuasiCompact g.base] [QuasiSeparated g.base]
    [AlgebraicGeometry.Scheme.Hom.FiniteType B.sourceToClosed]
    [QuasiSeparated B.sourceToClosed] :
    ∃ i₀ : ℕ, ∀ (F : RingedSite.ModuleCat.{u + 1} B.ringedSite)
      [IsCrystalInQuasiCoherentModules F] (i : ℕ),
      i₀ < i → CategoryTheory.Limits.IsZero
        (RingedSite.ToposHom.higherDirectImageModule.{u + 1, u, u + 1, u, u + 1}
          (Ringed.morphism B B' g hbase f hf) F i) :=
  sorry

