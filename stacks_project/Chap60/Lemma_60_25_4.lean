/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AlphaP
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Abelian
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
variable (h_p_mem : ∀ V : B.scheme.affineOpens, (p : Γ(B.scheme, V)) ∈ B.ideal.ideal V)
variable {X' : Scheme.{u}} (f : X' ⟶ B.source) (x'₀ : X' ⟶ B.ideal.subscheme)
variable (h_over : f ≫ B.sourceToClosed = x'₀)
variable [Scheme.IsCharP B.source p] [Scheme.IsCharP X' p]
variable [IsIteratedAlphaPCover p f]
variable [HasDerivedCategory.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1}
  (Sheaf (B.withSource X' x'₀ (B.prime_nilpotent_of_mem h_p_mem X' x'₀)).ringedSite.siteTopology
    AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1}
  (Sheaf (B.withSource X' x'₀ (B.prime_nilpotent_of_mem h_p_mem X' x'₀)).ringedSite.siteTopology
    AddCommGrpCat.{u + 1})]

/- Lemma 60.25.4. For an iterated `α_p`-cover of constant degree `q`, the
cohomology sheaves of every distinguished cone of the crystalline coefficient
comparison are annihilated by `q`. -/
@[stacks 07Q9] #check
  (AlgebraicGeometry.Scheme.Crystalline.iteratedAlphaPCover_cone_nsmul
    B h_p_mem f x'₀ h_over :
    ∀ (q : ℕ) [IsFiniteLocallyFreeOfRank f q]
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf)
    [IsCrystalInQuasiCoherentModules F]
    {E : DerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})}
    (g :
      (zariskiAbelianPushforwardExact.{u, u + 1} f
        (IsIteratedAlphaPCover.isHomeomorph p f)).mapDerivedCategory.obj
          (derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
            x'₀ (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
              ((SheafOfModules.toSheaf _).obj
                ((crystalPullback B f x'₀ h_over
                  (B.prime_nilpotent_of_mem h_p_mem X' x'₀)).obj F))) ⟶ E)
    (δ : E ⟶
      (derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent ((SheafOfModules.toSheaf _).obj F))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (crystallineComparison B f x'₀ h_over (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
        (IsIteratedAlphaPCover.isHomeomorph p f) F) g δ ∈
      distTriang (DerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}))),
    ∀ i : ℤ, (q : ℤ) • 𝟙
      ((DerivedCategory.homologyFunctor
        (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}) i).obj E) = 0)

end AlgebraicGeometry.Scheme.Crystalline
