/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AlphaP
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Smooth
public import ReasLib.AlgebraicGeometry.Crystalline.Frobenius.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Replace the source of a crystalline base by its Frobenius twist over the closed fibre,
retaining the divided-power base and using the second pullback projection. -/
@[reducible]
def Base.frobeniusTwist {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    [Scheme.IsCharP B.ideal.subscheme p] : Base.{u} p :=
  B.withSource (relativeFrobeniusTarget (p := p) B.sourceToClosed)
    (pullback.snd B.sourceToClosed (Scheme.absoluteFrobenius p B.ideal.subscheme))
    (Frobenius.twistPrimeNilpotent B.sourceToClosed B.prime_nilpotent)

/-- For a smooth morphism of relative dimension `d` over the characteristic-`p` closed
fibre of a divided-power base whose ideal contains `p`, the kernel of relative Frobenius
pullback on degree-`i` crystalline cohomology of any quasi-coherent crystal is annihilated
by `p ^ (d * (i + 1))`. -/
theorem relativeFrobenius_crystallineCohomology_kernel_nsmul
    {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    [Scheme.IsCharP B.ideal.subscheme p] {d : ℕ}
    (h_p_mem : ∀ V : B.scheme.affineOpens, (p : Γ(B.scheme, V)) ∈ B.ideal.ideal V)
    [SmoothOfRelativeDimension d B.sourceToClosed] [Scheme.IsCharP B.source p]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.frobeniusTwist.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf (B.frobeniusTwist.withSource B.source B.sourceToClosed
        (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)).ringedSite.siteTopology
          AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.frobeniusTwist.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1}
      (Sheaf B.frobeniusTwist.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1}
      (Sheaf (B.frobeniusTwist.withSource B.source B.sourceToClosed
        (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)).ringedSite.siteTopology
          AddCommGrpCat.{u + 1})]
    (G : SheafOfModules.{u + 1} B.frobeniusTwist.liftedStructureSheaf)
    [IsCrystalInQuasiCoherentModules G] (i : ℕ) :
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (kernel
        (crystallineCohomologyPullback B.frobeniusTwist
          (relativeFrobenius (p := p) B.sourceToClosed) B.sourceToClosed
          (relativeFrobenius_snd (p := p) B.sourceToClosed)
          (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)
          (Scheme.Hom.isHomeomorph (relativeFrobenius (p := p) B.sourceToClosed)) G i)) = 0 := sorry

/-- For a smooth morphism of relative dimension `d` over the characteristic-`p` closed
fibre of a divided-power base whose ideal contains `p`, the cokernel of relative Frobenius
pullback on degree-`i` crystalline cohomology of any quasi-coherent crystal is annihilated
by `p ^ (d * (i + 1))`. -/
theorem relativeFrobenius_crystallineCohomology_cokernel_nsmul
    {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    [Scheme.IsCharP B.ideal.subscheme p] {d : ℕ}
    (h_p_mem : ∀ V : B.scheme.affineOpens, (p : Γ(B.scheme, V)) ∈ B.ideal.ideal V)
    [SmoothOfRelativeDimension d B.sourceToClosed] [Scheme.IsCharP B.source p]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.frobeniusTwist.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf (B.frobeniusTwist.withSource B.source B.sourceToClosed
        (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)).ringedSite.siteTopology
          AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.frobeniusTwist.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{u + 1}
      (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1}
      (Sheaf B.frobeniusTwist.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1}
      (Sheaf (B.frobeniusTwist.withSource B.source B.sourceToClosed
        (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)).ringedSite.siteTopology
          AddCommGrpCat.{u + 1})]
    (G : SheafOfModules.{u + 1} B.frobeniusTwist.liftedStructureSheaf)
    [IsCrystalInQuasiCoherentModules G] (i : ℕ) :
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (cokernel
        (crystallineCohomologyPullback B.frobeniusTwist
          (relativeFrobenius (p := p) B.sourceToClosed) B.sourceToClosed
          (relativeFrobenius_snd (p := p) B.sourceToClosed)
          (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)
          (Scheme.Hom.isHomeomorph (relativeFrobenius (p := p) B.sourceToClosed)) G i)) = 0 := sorry

end AlgebraicGeometry.Scheme.Crystalline
