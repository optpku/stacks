/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Lemma_60_25_5
public import stacks_project.Chap60.Lemma_60_25_6_RelativeFrobenius
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open CategoryTheory.Functor.RightDerived
open SheafOfModules

universe u

/- Lemma 60.25.6 (1): if `f : X ⟶ S` is smooth of relative dimension `d` in prime
characteristic `p`, then the relative Frobenius `F_{X/S}` is an iterated
`α_p`-cover. -/
@[stacks 07QB] #check
  (relativeFrobenius_isIteratedAlphaPCover :
    {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
      [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
        IsIteratedAlphaPCover p (relativeFrobenius (p := p) f))

/- Lemma 60.25.6 (2): if `f : X ⟶ S` is smooth of relative dimension `d` in prime
characteristic `p`, then the relative Frobenius `F_{X/S}` has degree `p ^ d`. -/
@[stacks 07QB] #check
  (relativeFrobenius_isFiniteLocallyFreeOfRank_of_smooth :
    {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
      [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
        IsFiniteLocallyFreeOfRank (relativeFrobenius (p := p) f) (p ^ d))

noncomputable section

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable [Scheme.IsCharP I.subscheme p]
variable (h_p_twist :
  ∀ U : (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).affineOpens,
    IsNilpotent (p : Γ(@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance, U)))

/-- The pullback `F_{X/S₀}^*` on crystalline cohomology along the relative Frobenius
of `x₀ : X ⟶ S₀`. -/
def relativeFrobenius_crystallineCohomology_map
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [HasSheafify
      (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).op.HasPointwiseRightKanExtension
        P]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasLeftKanExtension
        P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
          (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance)
          h_p).op.HasPointwiseRightKanExtension
        P]
    [HasDerivedCategory
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
        AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          ((smallZariskiOpenFunctor (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (G :
      SheafOfModules
        (smallCrystallineStructureSheaf I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist))
    (i : ℕ) :=
  iteratedAlphaPCover_crystallineCohomology_map I γ h_compatible s
    (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
    (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance) h_p G i

/-- `relativeFrobenius_crystallineCohomology_map` is
`iteratedAlphaPCover_crystallineCohomology_map` along `F_{X/S₀}`. -/
theorem relativeFrobenius_crystallineCohomology_map_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [HasSheafify
      (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).op.HasPointwiseRightKanExtension
        P]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasLeftKanExtension
        P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
          (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance)
          h_p).op.HasPointwiseRightKanExtension
        P]
    [HasDerivedCategory
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
        AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          ((smallZariskiOpenFunctor (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (G :
      SheafOfModules
        (smallCrystallineStructureSheaf I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist))
    (i : ℕ) :
    relativeFrobenius_crystallineCohomology_map I γ h_compatible s x₀ h_p h_p_twist
        G i =
      iteratedAlphaPCover_crystallineCohomology_map I γ h_compatible s
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
        (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance) h_p G i :=
  sorry

/-- Lemma 60.25.6 (3): in Situation 60.7.5, if `p ∈ I` and `X ⟶ S₀` is smooth of
relative dimension `d`, then for a crystal `G` on `Cris(X⁽¹⁾/S)` the kernel of
`F_{X/S₀}^*` on `H^i` is annihilated by `p^(d * (i + 1))`. -/
@[stacks 07QB]
theorem relativeFrobenius_crystallineCohomology_kernel_nsmul
    {d : ℕ} (h_p_mem : ∀ V : S.affineOpens, (p : Γ(S, V)) ∈ I.ideal V)
    [SmoothOfRelativeDimension d x₀] [Scheme.IsCharP X p]
    [Scheme.IsCharP (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance) p]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [HasSheafify
      (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology AddCommGrpCat.{u}]
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [(smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U :
      smallCrystallineSite S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)),
      HasWeakSheafify
        ((smallCrystallineTopology p S I γ h_compatible s
            (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
            (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).over U)
        AddCommGrpCat.{u}]
    [∀ U :
      smallCrystallineSite S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)),
      ((smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).op.HasPointwiseRightKanExtension
        P]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasLeftKanExtension
        P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
          (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance)
          h_p).op.HasPointwiseRightKanExtension
        P]
    [HasDerivedCategory
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
        AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          ((smallZariskiOpenFunctor (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (G :
      SheafOfModules
        (smallCrystallineStructureSheaf I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist))
    [IsCrystalInQuasiCoherentModules G] (i : ℕ) :
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (kernel
        (relativeFrobenius_crystallineCohomology_map I γ h_compatible s x₀ h_p
          h_p_twist G i)) = 0 :=
  sorry

/-- Lemma 60.25.6 (4): in Situation 60.7.5, if `p ∈ I` and `X ⟶ S₀` is smooth of
relative dimension `d`, then for a crystal `G` on `Cris(X⁽¹⁾/S)` the cokernel of
`F_{X/S₀}^*` on `H^i` is annihilated by `p^(d * (i + 1))`. -/
@[stacks 07QB]
theorem relativeFrobenius_crystallineCohomology_cokernel_nsmul
    {d : ℕ} (h_p_mem : ∀ V : S.affineOpens, (p : Γ(S, V)) ∈ I.ideal V)
    [SmoothOfRelativeDimension d x₀] [Scheme.IsCharP X p]
    [Scheme.IsCharP (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance) p]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [HasSheafify
      (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology AddCommGrpCat.{u}]
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
      AddCommGrpCat.{u}]
    [(smallCrystallineTopology p S I γ h_compatible s
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U :
      smallCrystallineSite S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)),
      HasWeakSheafify
        ((smallCrystallineTopology p S I γ h_compatible s
            (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
            (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).over U)
        AddCommGrpCat.{u}]
    [∀ U :
      smallCrystallineSite S I γ h_compatible
        (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)),
      ((smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist).op.HasPointwiseRightKanExtension
        P]
    [∀ P :
      (smallCrystallineSite S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤
        AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasLeftKanExtension
        P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist x₀
          (@relativeFrobenius p inferInstance X I.subscheme x₀ inferInstance) (@relativeFrobenius_snd p inferInstance X I.subscheme x₀ inferInstance)
          h_p).op.HasPointwiseRightKanExtension
        P]
    [HasDerivedCategory
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf
        (smallCrystallineTopology p S I γ h_compatible s
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist)
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
        AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor
          (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          ((smallZariskiOpenFunctor (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance)).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf (@relativeFrobeniusTarget p inferInstance X I.subscheme x₀ inferInstance).smallZariskiTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (G :
      SheafOfModules
        (smallCrystallineStructureSheaf I γ h_compatible s
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) h_p_twist))
    [IsCrystalInQuasiCoherentModules G] (i : ℕ) :
    (p ^ (d * (i + 1)) : ℤ) • 𝟙
      (cokernel
        (relativeFrobenius_crystallineCohomology_map I γ h_compatible s x₀ h_p
          h_p_twist G i)) = 0 :=
  sorry


end AlgebraicGeometry.Scheme.Crystalline
