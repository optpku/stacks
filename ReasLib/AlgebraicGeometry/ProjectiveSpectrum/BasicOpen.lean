module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.StandardOpenCover

/-!
# Comparisons between basic-open charts of projective spectra

An inclusion between basic opens defined by positive-degree homogeneous elements induces
canonical comparison maps on ordinary and degree-zero localizations. This module also records
the corresponding localization equivalences, module maps, geometric compatibility, and finite
standard-open refinements.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry
open HomogeneousLocalization

noncomputable section

universe u v w z

namespace AlgebraicGeometry

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f g : A} {m n : ℕ}

/-- An inclusion `D₊(g) ⊆ D₊(f)` makes the image of `f` invertible in the ordinary
localization away from `g`. -/
theorem isUnit_localizationAway_of_basicOpen_le (hf : f ∈ 𝒜 m) (hm : 0 < m)
    (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    IsUnit (algebraMap A (Localization.Away g) f) := sorry

/-- An inclusion `D₊(g) ⊆ D₊(f)` makes the degree-zero fraction `f ^ n / g ^ m`
invertible in the homogeneous localization away from `g`. -/
theorem isUnit_homogeneousLocalizationAway_of_basicOpen_le
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    IsUnit (HomogeneousLocalization.Away.isLocalizationElem hg hf) := sorry

/-- Under an inclusion `D₊(g) ⊆ D₊(f)`, a positive power of `g` is a homogeneous
multiple of `f`. -/
theorem exists_homogeneous_multiple_of_basicOpen_le
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    ∃ e : ℕ, 0 < e ∧ ∃ a : 𝒜 (e * n - m), g ^ e = (a : A) * f := sorry

/-- The canonical algebra map from the localization away from `f` to the localization away
from `g`, associated to an inclusion `D₊(g) ⊆ D₊(f)`. -/
noncomputable def localizationAwayToAwayAlgHom
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    Localization.Away f →ₐ[A] Localization.Away g :=
  IsLocalization.Away.liftAlgHom
    (A := A) (S := Localization.Away f) (P := Localization.Away g)
    (f := Algebra.ofId A (Localization.Away g)) f
    (isUnit_localizationAway_of_basicOpen_le 𝒜 hf hm hg hn hgf)

/-- The ring-hom view of the canonical comparison between two ordinary localizations. -/
noncomputable def localizationAwayToAwayRingHom
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    Localization.Away f →+* Localization.Away g :=
  (localizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom

/-- The canonical ordinary comparison map agrees with the localization maps on elements of the
base ring. -/
theorem localizationAwayToAwayAlgHom_algebraMap
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (a : A) :
    localizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf
        (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away g) a := sorry

/-- The ring hom between degree-zero homogeneous localizations induced by an inclusion of
projective basic opens. -/
noncomputable def homogeneousLocalizationAwayToAwayRingHom
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    HomogeneousLocalization.Away 𝒜 f →+* HomogeneousLocalization.Away 𝒜 g := by
  let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
    (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (HomogeneousLocalization.Away 𝒜 g) (Localization.Away g))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp
    ((e.symm.toRingHom).comp
      (Subring.inclusion
        (show sourceMap.range ≤
            (algebraMap (HomogeneousLocalization.Away 𝒜 g) (Localization.Away g)).range from
          by sorry)))
    sourceMap.rangeRestrict

/-- The degree-zero comparison ring hom is compatible with the ordinary comparison after
forgetting the homogeneous grading. -/
theorem homogeneousLocalizationAwayToAwayRingHom_val
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
    (x : HomogeneousLocalization.Away 𝒜 f) :
    HomogeneousLocalization.val
        (homogeneousLocalizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf x) =
      localizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf
        (HomogeneousLocalization.val x) := sorry

/-- The degree-zero comparison ring hom commutes with the algebra maps from the degree-zero
piece of the graded ring. -/
theorem homogeneousLocalizationAwayToAwayRingHom_algebraMap
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (a : 𝒜 0) :
    homogeneousLocalizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf
        (algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 f) a) =
      algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 g) a := sorry

/-- The canonical comparison between degree-zero homogeneous localizations as an algebra hom
over the degree-zero piece. -/
noncomputable def homogeneousLocalizationAwayToAwayAlgHom
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    HomogeneousLocalization.Away 𝒜 f →ₐ[𝒜 0] HomogeneousLocalization.Away 𝒜 g where
  __ := homogeneousLocalizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf
  commutes' := homogeneousLocalizationAwayToAwayRingHom_algebraMap 𝒜 hf hm hg hn hgf

/-- The degree-zero comparison algebra hom is compatible with the ordinary comparison after
forgetting the homogeneous grading. -/
theorem homogeneousLocalizationAwayToAwayAlgHom_val
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
    (x : HomogeneousLocalization.Away 𝒜 f) :
    HomogeneousLocalization.val
        (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf x) =
      localizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf
        (HomogeneousLocalization.val x) := sorry

/-- The type of the canonical algebra equivalence from the localization of `A_(f)` at the
fraction `g ^ m / f ^ n` to `A_(g)`. -/
abbrev homogeneousLocalizationAwayToAwayAlgEquivType
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :=
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg) ≃ₐ[
    HomogeneousLocalization.Away 𝒜 f] HomogeneousLocalization.Away 𝒜 g

/-- The target degree-zero homogeneous localization has the universal property of localization
at the canonical fraction in the source. -/
theorem homogeneousLocalizationAwayToAwayAlgHom_isLocalization
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    -- Local instance justification (defeq pin): fixes the comparison algebra structure.
    let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
    IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (HomogeneousLocalization.Away 𝒜 g) := sorry

/-- Localizing `A_(f)` at the canonical fraction `g ^ m / f ^ n` gives the canonical algebra
equivalence with `A_(g)`. -/
noncomputable def homogeneousLocalizationAwayToAwayAlgEquiv
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    homogeneousLocalizationAwayToAwayAlgEquivType 𝒜 hf hm hg hn hgf := by
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  -- Local instance justification (defeq pin): fixes the ring localization structure.
  let _ : IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (HomogeneousLocalization.Away 𝒜 g) :=
    homogeneousLocalizationAwayToAwayAlgHom_isLocalization 𝒜 hf hm hg hn hgf
  exact IsLocalization.algEquiv
    (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem hf hg))
    (Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg))
    (HomogeneousLocalization.Away 𝒜 g)

/-- The canonical algebra equivalence acts by the equivalence supplied by the localization
universal property. -/
theorem homogeneousLocalizationAwayToAwayAlgEquiv_apply
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
    (x : Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)) :
    -- Local instance justification (defeq pin): fixes the comparison algebra structure.
    let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
    -- Local instance justification (defeq pin): fixes the ring localization structure.
    let _ : IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
        (HomogeneousLocalization.Away 𝒜 g) :=
      homogeneousLocalizationAwayToAwayAlgHom_isLocalization 𝒜 hf hm hg hn hgf
    homogeneousLocalizationAwayToAwayAlgEquiv 𝒜 hf hm hg hn hgf x =
      IsLocalization.algEquiv
        (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem hf hg))
        (Localization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg))
        (HomogeneousLocalization.Away 𝒜 g) x := sorry

/-- The canonical linear comparison map between ordinary localizations of a module. -/
noncomputable def localizationAwayToAwayModuleMap
    {M : Type w} [AddCommMonoid M] [Module A M]
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    -- Local instance justification (defeq pin): fixes the restricted scalar action.
    let _ : Module (Localization.Away f) (LocalizedModule.Away g M) :=
      Module.compHom (LocalizedModule.Away g M)
        (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf)
    LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away g M := by
  -- Local instance justification (defeq pin): fixes the restricted scalar action.
  let _ : Module (Localization.Away f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M)
      (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf)
  let baseMap := LocalizedModule.Away.mapOfIsUnit (M := M) f g
    (isUnit_localizationAway_of_basicOpen_le 𝒜 hf hm hg hn hgf)
  exact
    { toFun := baseMap
      map_add' := baseMap.map_add
      map_smul' := by sorry }

/-- The ordinary localized-module comparison sends an original module element to its canonical
image in the target localization. -/
theorem localizationAwayToAwayModuleMap_mkLinearMap
    {M : Type w} [AddCommMonoid M] [Module A M]
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) (x : M) :
    localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M x) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M x := sorry

/-- Restricting scalars from `A[f⁻¹]` to `A_(f)` gives the ambient module comparison map used
for degree-zero homogeneous localizations. -/
noncomputable def homogeneousLocalizationAwayToAwayAmbientModuleMap
    {M : Type w} [AddCommGroup M] [Module A M]
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
      (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
    -- Local instance justification (defeq pin): fixes the restricted scalar action.
    let _ : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away g M) :=
      Module.compHom (LocalizedModule.Away g M) sourceMap
    LocalizedModule.Away f M →ₗ[HomogeneousLocalization.Away 𝒜 f]
      LocalizedModule.Away g M := by
  -- Local instance justification (defeq pin): fixes the restricted scalar action.
  let _ : Module (Localization.Away f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M)
      (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf)
  let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
    (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  -- Local instance justification (defeq pin): fixes the restricted scalar action.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M) sourceMap
  exact
    { toFun := localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf
      map_add' := (localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf).map_add
      map_smul' := by sorry }

/-- The ambient module comparison preserves the degree-zero parts of the two homogeneous
localizations. -/
theorem homogeneousLocalizationAwayToAwayAmbientModuleMap_mem_awayDegreeZeroPart
    {M : Type w} [AddCommGroup M] [Module A M]
    {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
    (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) {x : LocalizedModule.Away f M}
    (hx : x ∈ HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩) :
    homogeneousLocalizationAwayToAwayAmbientModuleMap 𝒜 hf hm hg hn hgf x ∈
      HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩ := sorry

/-- The scalar action on the ambient target module is compatible with the degree-zero
comparison algebra map. -/
theorem homogeneousLocalizationAwayToAwayAmbientCodomain_isScalarTower
    {M : Type w} [AddCommGroup M] [Module A M]
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    -- Local instance justification (defeq pin): fixes the comparison algebra structure.
    let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
    let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
      (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
    -- Local instance justification (defeq pin): fixes the restricted scalar action.
    let _ : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away g M) :=
      Module.compHom (LocalizedModule.Away g M) sourceMap
    IsScalarTower (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g)
      (LocalizedModule.Away g M) := sorry

/-- The map on affine spectra induced by the degree-zero comparison is an open immersion. -/
theorem homogeneousLocalizationAwayToAwaySpecMap_isOpenImmersion
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    IsOpenImmersion
      (Spec.map
        (CommRingCat.ofHom
          (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom)) := sorry

/-- The morphism of projective basic opens induced by an inclusion of opens is an open
immersion. -/
theorem basicOpenHomOfLE_isOpenImmersion
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    IsOpenImmersion
      ((Proj 𝒜).homOfLE hgf : (Proj.basicOpen 𝒜 g).toScheme ⟶
        (Proj.basicOpen 𝒜 f).toScheme) := sorry

/-- The affine-chart identifications of two projective basic opens intertwine their inclusion
with the morphism induced by the degree-zero comparison algebra map. -/
theorem Proj.basicOpenIsoSpec_homOfLE
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    ((Proj.basicOpenIsoSpec 𝒜 g hg hn).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom)) =
      ((Proj 𝒜).homOfLE hgf : (Proj.basicOpen 𝒜 g).toScheme ⟶
        (Proj.basicOpen 𝒜 f).toScheme) ≫
        (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom := sorry

section DegreeZeroModule

variable {M : Type w} [AddCommGroup M] [Module A M]
variable {τ : Type z} [SetLike τ M] [AddSubmonoidClass τ M]
variable (ℳ : ℕ → τ) [SetLike.GradedSMul 𝒜 ℳ]

/-- The type of the canonical degree-zero module comparison over the map `A_(f) → A_(g)`. -/
abbrev homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :=
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
    (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  -- Local instance justification (defeq pin): fixes the restricted scalar action.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M) sourceMap
  -- Local instance justification (defeq pin): fixes the scalar tower for the ambient module.
  let _ : IsScalarTower (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g)
      (LocalizedModule.Away g M) :=
    homogeneousLocalizationAwayToAwayAmbientCodomain_isScalarTower 𝒜 hf hm hg hn hgf
  -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
    Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
  HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩ →ₗ[
    HomogeneousLocalization.Away 𝒜 f]
    HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩

/-- The canonical comparison between the degree-zero parts of two localized graded modules. -/
noncomputable def homogeneousLocalizationAwayToAwayDegreeZeroModuleMap
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType 𝒜 ℳ hf hm hg hn hgf := by
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  let sourceMap : HomogeneousLocalization.Away 𝒜 f →+* Localization.Away g :=
    (localizationAwayToAwayRingHom 𝒜 hf hm hg hn hgf).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  -- Local instance justification (defeq pin): fixes the restricted scalar action.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M) sourceMap
  -- Local instance justification (defeq pin): fixes the scalar tower for the ambient module.
  let _ : IsScalarTower (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g)
      (LocalizedModule.Away g M) :=
    homogeneousLocalizationAwayToAwayAmbientCodomain_isScalarTower 𝒜 hf hm hg hn hgf
  -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
    Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
  exact
    { toFun := fun x ↦
        ⟨homogeneousLocalizationAwayToAwayAmbientModuleMap 𝒜 hf hm hg hn hgf x,
          homogeneousLocalizationAwayToAwayAmbientModuleMap_mem_awayDegreeZeroPart
            𝒜 ℳ hf hm hg hn hgf x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by sorry }

/-- The degree-zero module comparison agrees with the ordinary localized-module comparison on
underlying elements. -/
theorem homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_val
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
    (x : HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩) :
    (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf x :
        LocalizedModule.Away g M) =
      localizationAwayToAwayModuleMap 𝒜 hf hm hg hn hgf x := sorry

/-- The target degree-zero localized module has the universal property of localization of the
source at the canonical fraction. -/
theorem homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    -- Local instance justification (defeq pin): fixes the comparison algebra structure.
    let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
    -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
    let _ : Module (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
      Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
        (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
    IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf) := sorry

/-- The type of the canonical linear equivalence obtained by localizing the degree-zero module
at the canonical fraction. -/
abbrev homogeneousLocalizationAwayToAwayDegreeZeroModuleEquivType
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :=
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
    Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
  -- Local instance justification (defeq pin): fixes the localized-module structure.
  let _ : IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf) :=
    homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule 𝒜 ℳ
      hf hm hg hn hgf
  LocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩) ≃ₗ[
        HomogeneousLocalization.Away 𝒜 f]
    HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩

/-- Localizing the source degree-zero module at the canonical fraction gives the canonical
linear equivalence with the target degree-zero module. -/
noncomputable def homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f) :
    homogeneousLocalizationAwayToAwayDegreeZeroModuleEquivType 𝒜 ℳ hf hm hg hn hgf := by
  -- Local instance justification (defeq pin): fixes the comparison algebra structure.
  let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
    (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
  -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
  let _ : Module (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
    Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
  -- Local instance justification (defeq pin): fixes the localized-module structure.
  let _ : IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
      (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf) :=
    homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule 𝒜 ℳ
      hf hm hg hn hgf
  exact
    IsLocalizedModule.iso
      (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem hf hg))
      (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf)

/-- The canonical module equivalence sends a generator of the localization to the degree-zero
comparison map applied to that generator. -/
theorem homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv_apply_mk
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hgf : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)
    (x : HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨f, hf⟩) :
    -- Local instance justification (defeq pin): fixes the comparison algebra structure.
    let _ : Algebra (HomogeneousLocalization.Away 𝒜 f) (HomogeneousLocalization.Away 𝒜 g) :=
      (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toAlgebra
    -- Local instance justification (defeq pin): fixes the restricted scalar action on degree zero.
    let _ : Module (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩) :=
      Module.compHom (HomogeneousLocalization.Away.Module.degreeZeroPart 𝒜 ℳ ⟨g, hg⟩)
        (homogeneousLocalizationAwayToAwayAlgHom 𝒜 hf hm hg hn hgf).toRingHom
    -- Local instance justification (defeq pin): fixes the localized-module structure.
    let _ : IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg)
        (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf) :=
      homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_isLocalizedModule 𝒜 ℳ
        hf hm hg hn hgf
    homogeneousLocalizationAwayToAwayDegreeZeroModuleEquiv 𝒜 ℳ hf hm hg hn hgf
        (LocalizedModule.mk x 1) =
      homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜 ℳ hf hm hg hn hgf x := sorry

end DegreeZeroModule

/-- Every open cover of a projective basic open admits a finite refinement by positive-degree
homogeneous basic opens. -/
theorem basicOpen_has_finite_refinement_of_open_cover
    (hf : f ∈ 𝒜 m) (hm : 0 < m) {ι : Type w}
    (U : ι → TopologicalSpace.Opens (ProjectiveSpectrum 𝒜))
    (hcover : Proj.basicOpen 𝒜 f ≤ ⨆ i, U i) :
    ∃ V : Proj.StandardOpenCoverOf 𝒜 f,
      ∀ i : V.index, ∃ j, Proj.basicOpen 𝒜 (V.generator i) ≤ U j := sorry

/-- A finite family of positive-degree homogeneous basic opens covers `D₊(f)` exactly when the
associated degree-zero fractions span the unit ideal of `A_(f)`. -/
theorem basicOpen_le_iSup_basicOpen_iff_span_eq_top
    (hf : f ∈ 𝒜 m) (hm : 0 < m) {N : ℕ}
    (gs : Fin N → A) (deg : Fin N → ℕ)
    (hgs : ∀ i, gs i ∈ 𝒜 (deg i)) (hdeg : ∀ i, 0 < deg i) :
    Proj.basicOpen 𝒜 f ≤ ⨆ i, Proj.basicOpen 𝒜 (gs i) ↔
      Ideal.span
          (Set.range fun i ↦
            (HomogeneousLocalization.Away.isLocalizationElem hf (hgs i) :
              HomogeneousLocalization.Away 𝒜 f)) =
        ⊤ := sorry

end

end AlgebraicGeometry
