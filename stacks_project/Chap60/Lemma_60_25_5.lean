/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AlphaP
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

noncomputable section

universe u

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

variable (q : ℕ) [IsFiniteLocallyFreeOfRank f q]
variable (F : SheafOfModules.{u + 1} B.liftedStructureSheaf)
variable [IsCrystalInQuasiCoherentModules F] (i : ℕ)

/- Lemma 60.25.5 (1): under the assumptions of Lemma 60.25.4, the kernel of the
canonical module-coefficient pullback on degree-`i` crystalline cohomology is annihilated by
`q ^ (i + 1)`. -/
@[stacks 07QA] #check
  (AlgebraicGeometry.Scheme.Crystalline.iteratedAlphaPCover_crystallineCohomology_kernel_nsmul
      B h_p_mem f x'₀ h_over q F i :
    (q ^ (i + 1) : ℤ) • 𝟙
      (kernel (AlgebraicGeometry.Scheme.Crystalline.crystallineCohomologyPullback
        B f x'₀ h_over (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
        (IsIteratedAlphaPCover.isHomeomorph p f) F i)) = 0)

/- Lemma 60.25.5 (2): under the assumptions of Lemma 60.25.4, the cokernel of the
canonical module-coefficient pullback on degree-`i` crystalline cohomology is annihilated by
`q ^ (i + 1)`. -/
@[stacks 07QA] #check
  (AlgebraicGeometry.Scheme.Crystalline.iteratedAlphaPCover_crystallineCohomology_cokernel_nsmul
      B h_p_mem f x'₀ h_over q F i :
    (q ^ (i + 1) : ℤ) • 𝟙
      (cokernel (AlgebraicGeometry.Scheme.Crystalline.crystallineCohomologyPullback
        B f x'₀ h_over (B.prime_nilpotent_of_mem h_p_mem X' x'₀)
        (IsIteratedAlphaPCover.isHomeomorph p f) F i)) = 0)

