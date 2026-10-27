/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Frobenius.Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

universe u

/- Lemma 60.25.6 (1): if `f : X ⟶ S` is smooth of relative dimension `d` in prime
characteristic `p`, then the relative Frobenius `F_{X/S}` is an iterated
`α_p`-cover. -/
@[stacks 07QB] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isIteratedAlphaPCover :
    {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
      [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
        IsIteratedAlphaPCover p (relativeFrobenius (p := p) f))

/- Lemma 60.25.6 (2): if `f : X ⟶ S` is smooth of relative dimension `d` in prime
characteristic `p`, then the relative Frobenius `F_{X/S}` has degree `p ^ d`. -/
@[stacks 07QB] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isFiniteLocallyFreeOfRank_of_smooth :
    {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
      [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
        IsFiniteLocallyFreeOfRank (relativeFrobenius (p := p) f) (p ^ d))

/- Lemma 60.25.6 (3): for every quasi-coherent crystal on the Frobenius twist,
the kernel of relative Frobenius pullback on `H^i` is annihilated by
`p ^ (d * (i + 1))`. -/
@[stacks 07QB] #check
  (AlgebraicGeometry.Scheme.Crystalline.relativeFrobenius_crystallineCohomology_kernel_nsmul :
    ∀ {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
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
    [IsCrystalInQuasiCoherentModules G] (i : ℕ),
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (kernel
        (crystallineCohomologyPullback B.frobeniusTwist
          (relativeFrobenius (p := p) B.sourceToClosed) B.sourceToClosed
          (relativeFrobenius_snd (p := p) B.sourceToClosed)
          (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)
          (Scheme.Hom.isHomeomorph (relativeFrobenius (p := p) B.sourceToClosed)) G i)) = 0)

/- Lemma 60.25.6 (4): for every quasi-coherent crystal on the Frobenius twist,
the cokernel of relative Frobenius pullback on `H^i` is annihilated by
`p ^ (d * (i + 1))`. -/
@[stacks 07QB] #check
  (AlgebraicGeometry.Scheme.Crystalline.relativeFrobenius_crystallineCohomology_cokernel_nsmul :
    ∀ {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
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
    [IsCrystalInQuasiCoherentModules G] (i : ℕ),
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (cokernel
        (crystallineCohomologyPullback B.frobeniusTwist
          (relativeFrobenius (p := p) B.sourceToClosed) B.sourceToClosed
          (relativeFrobenius_snd (p := p) B.sourceToClosed)
          (B.prime_nilpotent_of_mem h_p_mem B.source B.sourceToClosed)
          (Scheme.Hom.isHomeomorph (relativeFrobenius (p := p) B.sourceToClosed)) G i)) = 0)

