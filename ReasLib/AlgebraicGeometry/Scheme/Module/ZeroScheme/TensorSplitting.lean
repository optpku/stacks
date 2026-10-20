/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.ZeroSection
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Splittings of zero schemes of tensor-product sections

This file packages a geometric splitting of the zero scheme of a section of a
tensor product of two invertible modules. The chosen schemes, morphisms,
sections, and relative-spectrum models are data, while their geometric
properties are proposition-valued fields.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

/-- The restriction to `D` of the inverse tensor power of an invertible module
on `Y`. -/
noncomputable abbrev restrictedInverse
    {D Y : Scheme.{u}} (i : D ⟶ Y) (L : Y.Modules) [Invertible L] : D.Modules :=
  (pullback i).obj (tensorPowerInt L (-1))

/-- The restricted inverse of an invertible module is quasicoherent. -/
theorem restrictedInverse_isQuasicoherent
    {D Y : Scheme.{u}} (i : D ⟶ Y) (L : Y.Modules) [Invertible L] :
    (restrictedInverse i L).IsQuasicoherent := sorry

/-- The symmetric algebra of the restriction of the inverse of an invertible
module. -/
noncomputable def restrictedInverseSymmetricAlgebra
    {D Y : Scheme.{u}} (i : D ⟶ Y) (L : Y.Modules) [Invertible L] :
    D.QcAlgebraUnder :=
  @SymmetricAlgebra.qcAlgebra D (restrictedInverse i L)
    (restrictedInverse_isQuasicoherent i L)

end Modules

/-- A coherent splitting diagram for the zero scheme of a section of the
tensor product of two invertible modules. -/
structure TensorSectionSplitting.{v} {Y : Scheme.{v}}
    (L₁ L₂ : Y.Modules) [Modules.Invertible L₁] [Modules.Invertible L₂]
    (s : (L₁ ⊗ L₂).sections) where
  /-- The total scheme of the splitting. -/
  L : Scheme.{v}
  /-- The projection from the total scheme to the original scheme. -/
  p : L ⟶ Y
  /-- The first factor of the pulled-back tensor section. -/
  s₁ : ((Modules.pullback p).obj L₁).sections
  /-- The second factor of the pulled-back tensor section. -/
  s₂ : ((Modules.pullback p).obj L₂).sections
  /-- The map from the first factor's zero scheme to the base zero scheme. -/
  p₁ : zeroScheme ((Modules.pullback p).obj L₁) s₁ ⟶ zeroScheme (L₁ ⊗ L₂) s
  /-- The map from the second factor's zero scheme to the base zero scheme. -/
  p₂ : zeroScheme ((Modules.pullback p).obj L₂) s₂ ⟶ zeroScheme (L₁ ⊗ L₂) s
  /-- A relative-spectrum model for the first line over the base zero scheme. -/
  lineModel₁ : RelativeSpectrumOver
    (Modules.restrictedInverseSymmetricAlgebra (zeroSchemeι (L₁ ⊗ L₂) s) L₂)
  /-- A relative-spectrum model for the second line over the base zero scheme. -/
  lineModel₂ : RelativeSpectrumOver
    (Modules.restrictedInverseSymmetricAlgebra (zeroSchemeι (L₁ ⊗ L₂) s) L₁)
  /-- The first chosen model has the relative-spectrum universal property. -/
  lineModel₁_realizes : IsRelativeSpectrumOver lineModel₁
  /-- The second chosen model has the relative-spectrum universal property. -/
  lineModel₂_realizes : IsRelativeSpectrumOver lineModel₂
  /-- The first zero scheme is identified over the base with its line model. -/
  lineIso₁ : Over.mk p₁ ≅ Over.mk lineModel₁.π
  /-- The second zero scheme is identified over the base with its line model. -/
  lineIso₂ : Over.mk p₂ ≅ Over.mk lineModel₂.π
  /-- The scheme-theoretic intersection is identified with the base zero scheme. -/
  intersectionIso :
    Over.mk
        (Scheme.IdealSheafData.inclusion
            (le_sup_left :
              zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ≤
                zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
                  zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫ p₁) ≅
      Over.mk (𝟙 (zeroScheme (L₁ ⊗ L₂) s))
  /-- The first square of the splitting diagram commutes. -/
  left_comm : zeroSchemeι ((Modules.pullback p).obj L₁) s₁ ≫ p =
    p₁ ≫ zeroSchemeι (L₁ ⊗ L₂) s
  /-- The second square of the splitting diagram commutes. -/
  right_comm : zeroSchemeι ((Modules.pullback p).obj L₂) s₂ ≫ p =
    p₂ ≫ zeroSchemeι (L₁ ⊗ L₂) s
  /-- The pulled-back tensor section factors as the tensor of the two sections. -/
  section_factorization : Modules.pullbackTensorSection p s =
    RingedSpace.tensorSection s₁ s₂
  /-- The projection is of finite type. -/
  projection_finiteType : Hom.FiniteType p
  /-- The projection is flat. -/
  projection_flat : Flat p
  /-- The projection has relative dimension one. -/
  projection_relativeDimension : Hom.RelativeDimension p 1
  /-- The inverse image of the base zero scheme is the scheme-theoretic union
  of the two factor zero schemes. -/
  preimage_eq_union :
    (zeroIdealSheaf (L₁ ⊗ L₂) s).comap p =
      zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊓
        zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂
  /-- Under the intersection and line-model identifications, the first
  intersection inclusion is the zero section. -/
  zeroSection₁ : RelativeSpectrumOver.IsZeroSection
    (Modules.restrictedInverse_isQuasicoherent (zeroSchemeι (L₁ ⊗ L₂) s) L₂) lineModel₁
    (intersectionIso.inv.left ≫
      Scheme.IdealSheafData.inclusion
        (le_sup_left :
          zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ≤
            zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
              zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫
      lineIso₁.hom.left)
  /-- Under the intersection and line-model identifications, the second
  intersection inclusion is the zero section. -/
  zeroSection₂ : RelativeSpectrumOver.IsZeroSection
    (Modules.restrictedInverse_isQuasicoherent (zeroSchemeι (L₁ ⊗ L₂) s) L₁) lineModel₂
    (intersectionIso.inv.left ≫
      Scheme.IdealSheafData.inclusion
        (le_sup_right :
          zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂ ≤
            zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
              zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫
      lineIso₂.hom.left)

namespace TensorSectionSplitting

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
variable [Modules.Invertible L₁] [Modules.Invertible L₂]
variable {s : (L₁ ⊗ L₂).sections}

/-- Construct a tensor-section splitting from an explicit diagram, line
models, identifications, and the defining geometric properties. -/
def ofDiagram
    (L : Scheme.{u}) (p : L ⟶ Y)
    (s₁ : ((Modules.pullback p).obj L₁).sections)
    (s₂ : ((Modules.pullback p).obj L₂).sections)
    (p₁ : zeroScheme ((Modules.pullback p).obj L₁) s₁ ⟶ zeroScheme (L₁ ⊗ L₂) s)
    (p₂ : zeroScheme ((Modules.pullback p).obj L₂) s₂ ⟶ zeroScheme (L₁ ⊗ L₂) s)
    (lineModel₁ : RelativeSpectrumOver
      (Modules.restrictedInverseSymmetricAlgebra (zeroSchemeι (L₁ ⊗ L₂) s) L₂))
    (lineModel₂ : RelativeSpectrumOver
      (Modules.restrictedInverseSymmetricAlgebra (zeroSchemeι (L₁ ⊗ L₂) s) L₁))
    (lineModel₁_realizes : IsRelativeSpectrumOver lineModel₁)
    (lineModel₂_realizes : IsRelativeSpectrumOver lineModel₂)
    (lineIso₁ : Over.mk p₁ ≅ Over.mk lineModel₁.π)
    (lineIso₂ : Over.mk p₂ ≅ Over.mk lineModel₂.π)
    (intersectionIso :
      Over.mk
          (Scheme.IdealSheafData.inclusion
              (le_sup_left :
                zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ≤
                  zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
                    zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫ p₁) ≅
        Over.mk (𝟙 (zeroScheme (L₁ ⊗ L₂) s)))
    (left_comm : zeroSchemeι ((Modules.pullback p).obj L₁) s₁ ≫ p =
      p₁ ≫ zeroSchemeι (L₁ ⊗ L₂) s)
    (right_comm : zeroSchemeι ((Modules.pullback p).obj L₂) s₂ ≫ p =
      p₂ ≫ zeroSchemeι (L₁ ⊗ L₂) s)
    (section_factorization : Modules.pullbackTensorSection p s =
      RingedSpace.tensorSection s₁ s₂)
    (projection_finiteType : Hom.FiniteType p) (projection_flat : Flat p)
    (projection_relativeDimension : Hom.RelativeDimension p 1)
    (preimage_eq_union :
      (zeroIdealSheaf (L₁ ⊗ L₂) s).comap p =
        zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊓
          zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂)
    (zeroSection₁ : RelativeSpectrumOver.IsZeroSection
      (Modules.restrictedInverse_isQuasicoherent (zeroSchemeι (L₁ ⊗ L₂) s) L₂) lineModel₁
      (intersectionIso.inv.left ≫
        Scheme.IdealSheafData.inclusion
          (le_sup_left :
            zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ≤
              zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
                zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫
        lineIso₁.hom.left))
    (zeroSection₂ : RelativeSpectrumOver.IsZeroSection
      (Modules.restrictedInverse_isQuasicoherent (zeroSchemeι (L₁ ⊗ L₂) s) L₁) lineModel₂
      (intersectionIso.inv.left ≫
        Scheme.IdealSheafData.inclusion
          (le_sup_right :
            zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂ ≤
              zeroIdealSheaf ((Modules.pullback p).obj L₁) s₁ ⊔
                zeroIdealSheaf ((Modules.pullback p).obj L₂) s₂) ≫
        lineIso₂.hom.left)) :
    TensorSectionSplitting L₁ L₂ s where
  L := L
  p := p
  s₁ := s₁
  s₂ := s₂
  p₁ := p₁
  p₂ := p₂
  lineModel₁ := lineModel₁
  lineModel₂ := lineModel₂
  lineModel₁_realizes := lineModel₁_realizes
  lineModel₂_realizes := lineModel₂_realizes
  lineIso₁ := lineIso₁
  lineIso₂ := lineIso₂
  intersectionIso := intersectionIso
  left_comm := left_comm
  right_comm := right_comm
  section_factorization := section_factorization
  projection_finiteType := projection_finiteType
  projection_flat := projection_flat
  projection_relativeDimension := projection_relativeDimension
  preimage_eq_union := preimage_eq_union
  zeroSection₁ := zeroSection₁
  zeroSection₂ := zeroSection₂

/-- The zero scheme of the original tensor-product section. -/
noncomputable abbrev baseZero (_ : TensorSectionSplitting L₁ L₂ s) : Scheme.{u} :=
  zeroScheme (L₁ ⊗ L₂) s

/-- The canonical inclusion of the base zero scheme into `Y`. -/
noncomputable abbrev baseι (C : TensorSectionSplitting L₁ L₂ s) : C.baseZero ⟶ Y :=
  zeroSchemeι (L₁ ⊗ L₂) s

/-- The ideal defining the first factor zero scheme in the total space. -/
noncomputable abbrev ideal₁ (C : TensorSectionSplitting L₁ L₂ s) : C.L.IdealSheafData :=
  zeroIdealSheaf ((Modules.pullback C.p).obj L₁) C.s₁

/-- The ideal defining the second factor zero scheme in the total space. -/
noncomputable abbrev ideal₂ (C : TensorSectionSplitting L₁ L₂ s) : C.L.IdealSheafData :=
  zeroIdealSheaf ((Modules.pullback C.p).obj L₂) C.s₂

/-- The first factor zero scheme. -/
noncomputable abbrev zero₁ (C : TensorSectionSplitting L₁ L₂ s) : Scheme.{u} :=
  C.ideal₁.subscheme

/-- The second factor zero scheme. -/
noncomputable abbrev zero₂ (C : TensorSectionSplitting L₁ L₂ s) : Scheme.{u} :=
  C.ideal₂.subscheme

/-- The first factor zero scheme's inclusion into the total space. -/
noncomputable abbrev ι₁ (C : TensorSectionSplitting L₁ L₂ s) : C.zero₁ ⟶ C.L :=
  C.ideal₁.subschemeι

/-- The second factor zero scheme's inclusion into the total space. -/
noncomputable abbrev ι₂ (C : TensorSectionSplitting L₁ L₂ s) : C.zero₂ ⟶ C.L :=
  C.ideal₂.subschemeι

/-- The scheme-theoretic intersection of the two factor zero schemes. -/
noncomputable abbrev intersection (C : TensorSectionSplitting L₁ L₂ s) : Scheme.{u} :=
  Scheme.schemeTheoreticIntersection C.ideal₁ C.ideal₂

/-- The canonical map from the intersection to the first factor zero scheme. -/
noncomputable abbrev intersectionToZero₁ (C : TensorSectionSplitting L₁ L₂ s) :
    C.intersection ⟶ C.zero₁ :=
  Scheme.IdealSheafData.inclusion (le_sup_left : C.ideal₁ ≤ C.ideal₁ ⊔ C.ideal₂)

/-- The canonical map from the intersection to the second factor zero scheme. -/
noncomputable abbrev intersectionToZero₂ (C : TensorSectionSplitting L₁ L₂ s) :
    C.intersection ⟶ C.zero₂ :=
  Scheme.IdealSheafData.inclusion (le_sup_right : C.ideal₂ ≤ C.ideal₁ ⊔ C.ideal₂)

/-- The common map from the scheme-theoretic intersection to the base zero scheme. -/
noncomputable abbrev intersectionToBase (C : TensorSectionSplitting L₁ L₂ s) :
    C.intersection ⟶ C.baseZero :=
  C.intersectionToZero₁ ≫ C.p₁

/-- The two squares from the factor zero schemes through the total space and
the base zero scheme commute. -/
theorem diagram_spec (C : TensorSectionSplitting L₁ L₂ s) :
    C.ι₁ ≫ C.p = C.p₁ ≫ C.baseι ∧
      C.ι₂ ≫ C.p = C.p₂ ≫ C.baseι := sorry

/-- The first line model realizes the symmetric algebra of the restricted
inverse of the second factor and is identified with the first zero scheme. -/
theorem lineModel₁_spec (C : TensorSectionSplitting L₁ L₂ s) :
    IsRelativeSpectrumOver C.lineModel₁ ∧
      Nonempty (Over.mk C.p₁ ≅ Over.mk C.lineModel₁.π) := sorry

/-- The second line model realizes the symmetric algebra of the restricted
inverse of the first factor and is identified with the second zero scheme. -/
theorem lineModel₂_spec (C : TensorSectionSplitting L₁ L₂ s) :
    IsRelativeSpectrumOver C.lineModel₂ ∧
      Nonempty (Over.mk C.p₂ ≅ Over.mk C.lineModel₂.π) := sorry

/-- Functorial comparison data between a splitting and a splitting after base
change. -/
structure BaseChange.{v} {Y₀ : Scheme.{v}} {M₁ M₂ : Y₀.Modules}
    [Modules.Invertible M₁] [Modules.Invertible M₂]
    {t : (M₁ ⊗ M₂).sections} (C : TensorSectionSplitting M₁ M₂ t)
    {Y' : Scheme.{v}} (g : Y' ⟶ Y₀)
    (C' : TensorSectionSplitting ((Modules.pullback g).obj M₁)
      ((Modules.pullback g).obj M₂) (Modules.pullbackTensorSection g t)) where
  /-- The comparison map between total spaces. -/
  totalMap : C'.L ⟶ C.L
  /-- The comparison map between the base zero schemes. -/
  baseMap : C'.baseZero ⟶ C.baseZero
  /-- The comparison map between the first factor zero schemes. -/
  zeroMap₁ : C'.zero₁ ⟶ C.zero₁
  /-- The comparison map between the second factor zero schemes. -/
  zeroMap₂ : C'.zero₂ ⟶ C.zero₂
  /-- The total-space comparison square is cartesian. -/
  totalSquare : IsPullback totalMap C'.p C.p g
  /-- The base-zero-scheme comparison square is cartesian. -/
  baseSquare : IsPullback baseMap C'.baseι C.baseι g
  /-- The first factor-zero-scheme comparison square is cartesian. -/
  zeroSquare₁ : IsPullback zeroMap₁ C'.ι₁ C.ι₁ totalMap
  /-- The second factor-zero-scheme comparison square is cartesian. -/
  zeroSquare₂ : IsPullback zeroMap₂ C'.ι₂ C.ι₂ totalMap
  /-- The first vertical map is preserved by the comparison. -/
  p₁_compat : zeroMap₁ ≫ C.p₁ = C'.p₁ ≫ baseMap
  /-- The second vertical map is preserved by the comparison. -/
  p₂_compat : zeroMap₂ ≫ C.p₂ = C'.p₂ ≫ baseMap
  /-- The first factor section is transported by the cartesian comparison. -/
  section₁_compat : Modules.pullbackSectionAlongSquare totalSquare M₁ C.s₁ = C'.s₁
  /-- The second factor section is transported by the cartesian comparison. -/
  section₂_compat : Modules.pullbackSectionAlongSquare totalSquare M₂ C.s₂ = C'.s₂

namespace BaseChange

/-- Construct base-change compatibility from explicit comparison maps,
cartesian squares, diagram equations, and transported section equations. -/
def ofCartesian
    {C : TensorSectionSplitting L₁ L₂ s} {Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {C' : TensorSectionSplitting ((Modules.pullback g).obj L₁)
      ((Modules.pullback g).obj L₂) (Modules.pullbackTensorSection g s)}
    (totalMap : C'.L ⟶ C.L) (baseMap : C'.baseZero ⟶ C.baseZero)
    (zeroMap₁ : C'.zero₁ ⟶ C.zero₁) (zeroMap₂ : C'.zero₂ ⟶ C.zero₂)
    (totalSquare : IsPullback totalMap C'.p C.p g)
    (baseSquare : IsPullback baseMap C'.baseι C.baseι g)
    (zeroSquare₁ : IsPullback zeroMap₁ C'.ι₁ C.ι₁ totalMap)
    (zeroSquare₂ : IsPullback zeroMap₂ C'.ι₂ C.ι₂ totalMap)
    (p₁_compat : zeroMap₁ ≫ C.p₁ = C'.p₁ ≫ baseMap)
    (p₂_compat : zeroMap₂ ≫ C.p₂ = C'.p₂ ≫ baseMap)
    (section₁_compat : Modules.pullbackSectionAlongSquare totalSquare L₁ C.s₁ = C'.s₁)
    (section₂_compat : Modules.pullbackSectionAlongSquare totalSquare L₂ C.s₂ = C'.s₂) :
    BaseChange C g C' where
  totalMap := totalMap
  baseMap := baseMap
  zeroMap₁ := zeroMap₁
  zeroMap₂ := zeroMap₂
  totalSquare := totalSquare
  baseSquare := baseSquare
  zeroSquare₁ := zeroSquare₁
  zeroSquare₂ := zeroSquare₂
  p₁_compat := p₁_compat
  p₂_compat := p₂_compat
  section₁_compat := section₁_compat
  section₂_compat := section₂_compat

/-- The total-space comparison identifies the base-changed total scheme with
the categorical pullback. -/
noncomputable def totalIso
    {C : TensorSectionSplitting L₁ L₂ s} {Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {C' : TensorSectionSplitting ((Modules.pullback g).obj L₁)
      ((Modules.pullback g).obj L₂) (Modules.pullbackTensorSection g s)}
    (B : BaseChange C g C') : C'.L ≅ pullback C.p g :=
  B.totalSquare.isoPullback

/-- The base-zero comparison identifies the pulled-back zero scheme with the
categorical pullback. -/
noncomputable def baseIso
    {C : TensorSectionSplitting L₁ L₂ s} {Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {C' : TensorSectionSplitting ((Modules.pullback g).obj L₁)
      ((Modules.pullback g).obj L₂) (Modules.pullbackTensorSection g s)}
    (B : BaseChange C g C') : C'.baseZero ≅ pullback C.baseι g :=
  B.baseSquare.isoPullback

end BaseChange

end TensorSectionSplitting

/-- The zero scheme of a section of the tensor product of two invertible
modules admits a finite-type flat relative-dimension-one splitting into two
line bundles, with scheme-theoretic union and intersection properties, and the
construction is compatible with arbitrary same-universe base change. -/
theorem existsTensorSectionSplitting
    (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
    [Modules.Invertible L₁] [Modules.Invertible L₂]
    (s : (L₁ ⊗ L₂).sections) :
    ∃ C : TensorSectionSplitting L₁ L₂ s,
      ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
        ∃ C' : TensorSectionSplitting ((Modules.pullback g).obj L₁)
          ((Modules.pullback g).obj L₂) (Modules.pullbackTensorSection g s),
          Nonempty (C.BaseChange g C') := sorry

end AlgebraicGeometry.Scheme
