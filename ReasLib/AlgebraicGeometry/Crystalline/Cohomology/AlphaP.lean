/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Coefficients
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AlphaP
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

@[expose] public section

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

/-- For an iterated `α_p`-cover of constant degree `q` over a prime-local
divided-power base with `p` in its ideal, every distinguished cone of the
canonical derived comparison for a quasi-coherent crystal has all its
cohomology sheaves annihilated by `q`. -/
theorem iteratedAlphaPCover_cone_nsmul (q : ℕ) [IsFiniteLocallyFreeOfRank f q]
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
      distTriang (DerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}))) :
    ∀ i : ℤ, (q : ℤ) • 𝟙
      ((DerivedCategory.homologyFunctor
        (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}) i).obj E) = 0 := sorry

/-- For an iterated `α_p`-cover of constant degree `q` over a divided-power base with `p`
in its ideal, the kernel of pullback on degree-`i` crystalline cohomology of a quasi-coherent
crystal is annihilated by `q ^ (i + 1)`. -/
theorem iteratedAlphaPCover_crystallineCohomology_kernel_nsmul
    (q : ℕ) [IsFiniteLocallyFreeOfRank f q]
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf)
    [IsCrystalInQuasiCoherentModules F] (i : ℕ) :
    (q ^ (i + 1) : ℤ) • 𝟙
      (CategoryTheory.Limits.kernel
        (crystallineCohomologyPullback B f x'₀ h_over
          (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
          (IsIteratedAlphaPCover.isHomeomorph p f) F i)) = 0 := sorry

/-- For an iterated `α_p`-cover of constant degree `q` over a divided-power base with `p`
in its ideal, the cokernel of pullback on degree-`i` crystalline cohomology of a quasi-coherent
crystal is annihilated by `q ^ (i + 1)`. -/
theorem iteratedAlphaPCover_crystallineCohomology_cokernel_nsmul
    (q : ℕ) [IsFiniteLocallyFreeOfRank f q]
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf)
    [IsCrystalInQuasiCoherentModules F] (i : ℕ) :
    (q ^ (i + 1) : ℤ) • 𝟙
      (CategoryTheory.Limits.cokernel
        (crystallineCohomologyPullback B f x'₀ h_over
          (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
          (IsIteratedAlphaPCover.isHomeomorph p f) F i)) = 0 := sorry

end AlgebraicGeometry.Scheme.Crystalline
