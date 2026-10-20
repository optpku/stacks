/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.UpperResolution.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Upper-truncation resolutions by localized generators

The localized-generator object property and the property-neutral upper-resolution construction are
owned by separate leaves.  This file is the source-facing bridge that packages them for a ringed
site, so later arguments can request the resolution without rebuilding the generator closure API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- Lemma 21.17.10 (077J): every module complex admits a localized-generator upper resolution
whose sequential-colimit comparison is a quasi-isomorphism. -/
@[stacks 077J "upper resolution by localized generators"]
theorem exists_upperResolution_of_localizedGenerators
    (𝒢 : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) :
    ∃ S : CochainComplex.UpperTruncation.Resolution
        (localizedGeneratorCoproducts 𝒪) 𝒢,
      QuasiIso S.fromColimit := sorry

end SheafOfModules.RingedSite
