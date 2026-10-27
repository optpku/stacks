/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.DerivedSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
variable {X' : Scheme.{u}} (f : X' ⟶ B.source) (x'₀ : X' ⟶ B.ideal.subscheme)
variable (h_over : f ≫ B.sourceToClosed = x'₀)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))
variable [HasDerivedCategory.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1}
  (Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1}
  (Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})]

/-- Pullback on crystalline cohomology along a homeomorphism over a fixed divided-power
base, with module coefficients pulled back by inverse image and extension of scalars. -/
def crystallineCohomologyPullback (hf : IsHomeomorph f)
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf) (i : ℕ) :
    crystallineCohomology B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent ((SheafOfModules.toSheaf _).obj F) i ⟶
      crystallineCohomology B.ideal B.dividedPowers B.compatible B.toSpec
        x'₀ h_p' ((SheafOfModules.toSheaf _).obj
          ((crystalPullback B f x'₀ h_over h_p').obj F)) i :=
  let R : DerivedCategory.{u + 1}
      (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}) ⥤
        DerivedCategory AddCommGrpCat.{u + 1} :=
    siteAbelianSectionsDerivedWith B.source.smallZariskiTopology
      ((smallZariskiOpenFunctor B.source).obj ⊤)
  let M := derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1}
    B.ideal B.dividedPowers B.compatible B.toSpec x'₀ h_p'
      ((SheafOfModules.toSheaf _).obj ((crystalPullback B f x'₀ h_over h_p').obj F))
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
    (R.map (crystallineComparison B f x'₀ h_over h_p' hf F) ≫
      (zariskiAbelianDerivedSectionsPushforwardIso f hf).hom.app M)

/-- Crystalline cohomological pullback is homology of the module-adjunction comparison
followed by the canonical identification of derived global sections of a Zariski direct image. -/
theorem crystallineCohomologyPullback_spec (hf : IsHomeomorph f)
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf) (i : ℕ) :
    crystallineCohomologyPullback B f x'₀ h_over h_p' hf F i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
        ((siteAbelianSectionsDerivedWith B.source.smallZariskiTopology
            ((smallZariskiOpenFunctor B.source).obj ⊤)).map
            (crystallineComparison B f x'₀ h_over h_p' hf F) ≫
          (zariskiAbelianDerivedSectionsPushforwardIso f hf).hom.app
            (derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1}
              B.ideal B.dividedPowers B.compatible B.toSpec x'₀ h_p'
                ((SheafOfModules.toSheaf _).obj
                  ((crystalPullback B f x'₀ h_over h_p').obj F)))) := sorry

end AlgebraicGeometry.Scheme.Crystalline
