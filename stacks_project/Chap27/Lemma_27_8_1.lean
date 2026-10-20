/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.BasicOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v w z

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/- Lemma 27.8.1: an inclusion of positive-degree projective basic opens induces the
canonical localization comparisons, their geometric and module compatibilities, finite
standard-open refinements, and the degree-zero unit-ideal covering criterion. -/
@[stacks 01M4] #check
  (AlgebraicGeometry.isUnit_localizationAway_of_basicOpen_le :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      IsUnit (algebraMap A (Localization.Away g) f))

#check
  (AlgebraicGeometry.isUnit_homogeneousLocalizationAway_of_basicOpen_le :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m), 0 < m → ∀ (hg : g ∈ 𝒜 n), 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      IsUnit (HomogeneousLocalization.Away.isLocalizationElem hg hf))

#check
  (AlgebraicGeometry.exists_homogeneous_multiple_of_basicOpen_le :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      ∃ e : ℕ, 0 < e ∧ ∃ a : 𝒜 (e * n - m), g ^ e = (a : A) * f)

#check
  (AlgebraicGeometry.localizationAwayToAwayAlgHom :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      Localization.Away f →ₐ[A] Localization.Away g)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      HomogeneousLocalization.Away 𝒜 f →ₐ[𝒜 0] HomogeneousLocalization.Away 𝒜 g)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom_val :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
        (x : HomogeneousLocalization.Away 𝒜 f),
      HomogeneousLocalization.val
          (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
            𝒜 hf hm hg hn hgf x) =
        AlgebraicGeometry.localizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf (HomogeneousLocalization.val x))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgEquiv :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgEquivType
        𝒜 hf hm hg hn hgf)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwaySpecMap_isOpenImmersion :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f,
      IsOpenImmersion
        (Spec.map
          (CommRingCat.ofHom
            (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
              𝒜 hf hm hg hn hgf).toRingHom)))

#check
  (AlgebraicGeometry.basicOpenHomOfLE_isOpenImmersion :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      ∀ hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f,
      IsOpenImmersion
        ((Proj 𝒜).homOfLE hgf : (Proj.basicOpen 𝒜 g).toScheme ⟶
          (Proj.basicOpen 𝒜 f).toScheme))

#check
  (AlgebraicGeometry.Proj.basicOpenIsoSpec_homOfLE :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      ((Proj.basicOpenIsoSpec 𝒜 g hg hn).hom ≫
          Spec.map
            (CommRingCat.ofHom
              (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
                𝒜 hf hm hg hn hgf).toRingHom)) =
        ((Proj 𝒜).homOfLE hgf : (Proj.basicOpen 𝒜 g).toScheme ⟶
          (Proj.basicOpen 𝒜 f).toScheme) ≫
          (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom)

#check
  (AlgebraicGeometry.localizationAwayToAwayModuleMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommMonoid M] [Module A M],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      @LinearMap (Localization.Away f) (Localization.Away f)
        inferInstance inferInstance (RingHom.id (Localization.Away f))
        (LocalizedModule.Away f M) (LocalizedModule.Away g M)
        inferInstance inferInstance inferInstance
        (Module.compHom (LocalizedModule.Away g M)
          (AlgebraicGeometry.localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf)))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType
        𝒜 ℳ hf hm hg hn hgf)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_val :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
        (x : HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩),
      (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap
          𝒜 ℳ hf hm hg hn hgf x : LocalizedModule.Away g M) =
        AlgebraicGeometry.localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf x)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleEquivType
        𝒜 ℳ hf hm hg hn hgf)

#check
  (AlgebraicGeometry.basicOpen_has_finite_refinement_of_open_cover :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {m : ℕ},
      f ∈ 𝒜 m → 0 < m → ∀ {ι : Type w},
      ∀ (U : ι → TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)),
      Proj.basicOpen 𝒜 f ≤ ⨆ i, U i →
      ∃ V : Proj.StandardOpenCoverOf 𝒜 f,
        ∀ i : V.index, ∃ j, Proj.basicOpen 𝒜 (V.generator i) ≤ U j)

#check
  (AlgebraicGeometry.basicOpen_le_iSup_basicOpen_iff_span_eq_top :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {m : ℕ},
      ∀ (hf : f ∈ 𝒜 m), 0 < m → ∀ {N : ℕ}
        (gs : Fin N → A) (deg : Fin N → ℕ),
      ∀ (hgs : ∀ i, gs i ∈ 𝒜 (deg i)), (∀ i, 0 < deg i) →
      (Proj.basicOpen 𝒜 f ≤ ⨆ i, Proj.basicOpen 𝒜 (gs i) ↔
          Ideal.span
              (Set.range fun i ↦
                (HomogeneousLocalization.Away.isLocalizationElem hf (hgs i) :
                  HomogeneousLocalization.Away 𝒜 f)) =
            ⊤))

#check
  (AlgebraicGeometry.localizationAwayToAwayRingHom :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      Localization.Away f →+* Localization.Away g)

#check
  (AlgebraicGeometry.localizationAwayToAwayAlgHom_algebraMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (a : A),
      AlgebraicGeometry.localizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf
          (algebraMap A (Localization.Away f) a) =
        algebraMap A (Localization.Away g) a)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayRingHom :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f →
      HomogeneousLocalization.Away 𝒜 f →+* HomogeneousLocalization.Away 𝒜 g)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayRingHom_val :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
        (x : HomogeneousLocalization.Away 𝒜 f),
      HomogeneousLocalization.val
          (AlgebraicGeometry.homogeneousLocalizationAwayToAwayRingHom
            𝒜 hf hm hg hn hgf x) =
        AlgebraicGeometry.localizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf (HomogeneousLocalization.val x))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayRingHom_algebraMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (a : 𝒜 0),
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf
          (algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 f) a) =
        algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 g) a)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgEquivType :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f → Type u)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom_isLocalization :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonAlgebra : Algebra (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away 𝒜 g) :=
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf).toAlgebra
      IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
        (HomogeneousLocalization.Away 𝒜 g))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgEquiv_apply :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ},
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
        (x : Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)),
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonAlgebra : Algebra (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away 𝒜 g) :=
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf).toAlgebra
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _targetLocalization : IsLocalization.Away
          (HomogeneousLocalization.Away.isLocalizationElem hf hg)
          (HomogeneousLocalization.Away 𝒜 g) :=
        AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom_isLocalization
          𝒜 hf hm hg hn hgf
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgEquiv 𝒜 hf hm hg hn hgf x =
        IsLocalization.algEquiv
          (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem hf hg))
          (Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg))
          (HomogeneousLocalization.Away 𝒜 g) x)

#check
  (AlgebraicGeometry.localizationAwayToAwayModuleMap_mkLinearMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommMonoid M] [Module A M],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (x : M),
      AlgebraicGeometry.localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M x) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M x)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAmbientModuleMap :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
        (AlgebraicGeometry.localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonModule : Module (HomogeneousLocalization.Away 𝒜 f)
          (LocalizedModule.Away g M) :=
        Module.compHom (LocalizedModule.Away g M) sourceMap
      LocalizedModule.Away f M →ₗ[HomogeneousLocalization.Away 𝒜 f]
        LocalizedModule.Away g M)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAmbientModuleMap_mem_awayDegreeZeroPart :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) {x : LocalizedModule.Away f M},
      x ∈ HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩ →
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayAmbientModuleMap
          𝒜 hf hm hg hn hgf x ∈
        HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAmbientCodomain_isScalarTower :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonAlgebra : Algebra (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away 𝒜 g) :=
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf).toAlgebra
      let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
        (AlgebraicGeometry.localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonModule : Module (HomogeneousLocalization.Away 𝒜 f)
          (LocalizedModule.Away g M) :=
        Module.compHom (LocalizedModule.Away g M) sourceMap
      IsScalarTower (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) (LocalizedModule.Away g M))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f → Type (max u w))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
        (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f),
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonAlgebra : Algebra (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away 𝒜 g) :=
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf).toAlgebra
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _degreeZeroTargetModule : Module (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
        Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
          (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
            𝒜 hf hm hg hn hgf).toRingHom
      IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap
          𝒜 ℳ hf hm hg hn hgf))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleEquivType :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      f ∈ 𝒜 m → 0 < m → g ∈ 𝒜 n → 0 < n →
      Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f → Type (max u w))

#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv_apply_mk :
    ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {m n : ℕ}
      {M : Type w} [AddCommGroup M] [Module A M]
      {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
      (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ],
      ∀ (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n),
      ∀ (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
        (x : HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩),
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _comparisonAlgebra : Algebra (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away 𝒜 g) :=
        (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
          𝒜 hf hm hg hn hgf).toAlgebra
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _degreeZeroTargetModule : Module (HomogeneousLocalization.Away 𝒜 f)
          (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
        Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
          (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom
            𝒜 hf hm hg hn hgf).toRingHom
      -- Local instance justification (defeq pin): named instance needed to spell the complete dependent expected type without a placeholder
      letI _targetLocalizedModule : IsLocalizedModule.Away
          (HomogeneousLocalization.Away.isLocalizationElem hf hg)
          (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap
            𝒜 ℳ hf hm hg hn hgf) :=
        AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule
          𝒜 ℳ hf hm hg hn hgf
      AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv
          𝒜 ℳ hf hm hg hn hgf (LocalizedModule.mk x 1) =
        AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap
          𝒜 ℳ hf hm hg hn hgf x)

end
