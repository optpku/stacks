/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TensorSplitting.FirstProjection
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting.Unit

/-!
# Chow pullback for unit-factor tensor-section splittings

This file transports the first-projection pullback to the zero scheme of the
original section and records injectivity and compatibility with Gysin pullback,
including after locally finite-type base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.TensorSectionSplitting

open Scheme.TensorSectionSplitting

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (delta : S → ℤ) [IsDimensionFunction delta]
variable (X : Over S) [LocallyOfFiniteType X.hom]
variable (L : X.left.Modules) [Scheme.Modules.Invertible L]
variable (s : L.sections)
variable (C : Scheme.TensorSectionSplitting (𝟙_ X.left.Modules) L
  (Scheme.Modules.unitTensorSection L s))

/-- The first zero scheme of a locally finite-type raw pullback splitting is
locally noetherian over the fixed base. -/
theorem pullbackZero₁Over_isLocallyNoetherian
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s))) :
    IsLocallyNoetherian (pullbackZero₁Over X f L s C).left := sorry

/-- The relative grading on the first zero scheme of a raw pullback splitting
is a dimension function. -/
theorem pullbackZero₁Over_isDimensionFunction
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s))) :
    IsDimensionFunction
      (@Scheme.Hom.relativeDimensionFunction _ _ (pullbackZero₁Over X f L s C).hom
        (pullbackZero₁Over_locallyOfFiniteType X f L s C) delta) := sorry

/-- Degree-normalized first-projection pullback transported from the splitting's
base zero scheme to the zero scheme of the original section. -/
noncomputable def unitProjectionPullback
    (e : C.baseZero ≅ Scheme.zeroScheme L s)
    (h_e : e.hom ≫ Scheme.zeroSchemeι L s = C.baseι) (k : ℤ) :
    RelativeChow delta (Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (k - 1) →+
      @RelativeChow S inferInstance delta inferInstance (zero₁Over X C)
        (zero₁Over_locallyOfFiniteType X C) k :=
  (firstProjectionPullback delta X C k).comp
    (@ChowGroup.map S inferInstance delta inferInstance
      (Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (baseZeroOver X C)
      inferInstance (baseZeroOver_locallyOfFiniteType X C)
      (Scheme.TensorSectionSplitting.unitBaseZeroOverIso X L s C e h_e).inv
      inferInstance (k - 1))

/-- The transported first-projection pullback agrees with flat pullback along
the transported projection, followed by degree normalization. -/
theorem unitProjectionPullback_def
    (e : C.baseZero ≅ Scheme.zeroScheme L s)
    (h_e : e.hom ≫ Scheme.zeroSchemeι L s = C.baseι) (k : ℤ) :
    unitProjectionPullback delta X L s C e h_e k =
      (@ChowGroup.reindex (zero₁Over X C).left
        (zero₁Over_isLocallyNoetherian X C)
        (@Scheme.Hom.relativeDimensionFunction _ _ (zero₁Over X C).hom
          (zero₁Over_locallyOfFiniteType X C) delta)
        (zero₁Over_isDimensionFunction delta X C)
        ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
      (@ChowGroup.flatPullback S inferInstance delta inferInstance
        (zero₁Over X C) (Over.mk (Scheme.zeroSchemeι L s ≫ X.hom))
        (zero₁Over_locallyOfFiniteType X C) inferInstance
        (Scheme.TensorSectionSplitting.unitProjectionOver X L s C e h_e) 1
        (Scheme.TensorSectionSplitting.unitProjectionOver_flat X L s C e h_e)
        (Scheme.TensorSectionSplitting.unitProjectionOver_relativeDimension
          X L s C e h_e) (k - 1)) := sorry

/-- Degree-normalized first-projection pullback for a raw base-changed
unit-factor splitting, transported to the normalized pulled-back zero scheme. -/
noncomputable def pullbackUnitProjectionPullback
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [h_unit : Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [h_L : Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ Scheme.zeroScheme ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s) = C.baseι) (k : ℤ) :
    RelativeChow delta
        (Over.mk (Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
          (Scheme.Modules.sectionsPullback f L s) ≫ (f ≫ X.hom))) (k - 1) →+
      @RelativeChow S inferInstance delta inferInstance
        (pullbackZero₁Over X f L s C)
        (Scheme.TensorSectionSplitting.pullbackZero₁Over_locallyOfFiniteType
          X f L s C) k :=
  (@firstProjectionPullback S inferInstance delta inferInstance
      (Over.mk (f ≫ X.hom)) inferInstance
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L) h_unit h_L
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)) C k).comp
    (@ChowGroup.map S inferInstance delta inferInstance
      (Over.mk (Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
        (Scheme.Modules.sectionsPullback f L s) ≫ (f ≫ X.hom)))
      (@baseZeroOver S (Over.mk (f ≫ X.hom))
        ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
        ((Scheme.Modules.pullback f).obj L) h_unit h_L
        (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)) C)
      inferInstance
      (@baseZeroOver_locallyOfFiniteType S (Over.mk (f ≫ X.hom))
        ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
        ((Scheme.Modules.pullback f).obj L) h_unit h_L
        (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s))
        C inferInstance)
      (Scheme.TensorSectionSplitting.pullbackUnitBaseZeroOverIso
        X f L s C e h_e).inv inferInstance (k - 1))

/-- The raw base-change pullback agrees with flat pullback along the transported
projection, followed by degree normalization. -/
theorem pullbackUnitProjectionPullback_def
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ Scheme.zeroScheme ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s) = C.baseι) (k : ℤ) :
    pullbackUnitProjectionPullback delta X L s f C e h_e k =
      (@ChowGroup.reindex C.zero₁
        (pullbackZero₁Over_isLocallyNoetherian X L s f C)
        (@Scheme.Hom.relativeDimensionFunction _ _ (pullbackZero₁Over X f L s C).hom
        (pullbackZero₁Over_locallyOfFiniteType X f L s C) delta)
        (pullbackZero₁Over_isDimensionFunction delta X L s f C)
        ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
      (@ChowGroup.flatPullback S inferInstance delta inferInstance
        (pullbackZero₁Over X f L s C)
        (Over.mk (Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
          (Scheme.Modules.sectionsPullback f L s) ≫ (f ≫ X.hom)))
        (Scheme.TensorSectionSplitting.pullbackZero₁Over_locallyOfFiniteType
          X f L s C) inferInstance
        (Scheme.TensorSectionSplitting.pullbackUnitProjectionOver X L s f C e h_e) 1
        (Scheme.TensorSectionSplitting.pullbackUnitProjectionOver_flat
          X L s f C e h_e)
        (Scheme.TensorSectionSplitting.pullbackUnitProjectionOver_relativeDimension
          X L s f C e h_e) (k - 1)) := sorry

/-- The transported first-projection pullback for a raw base-changed splitting
is injective in every degree. -/
theorem pullbackUnitProjectionPullback_injective
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ Scheme.zeroScheme ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s) = C.baseι) (k : ℤ) :
    Function.Injective
      (pullbackUnitProjectionPullback delta X L s f C e h_e k) := sorry

/-- For a raw base-changed splitting, first-factor Gysin pullback commutes with
projection pullback after transport to the normalized pulled-back zero scheme. -/
theorem gysin_pullbackUnitProjectionPullback
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [h_unit : Scheme.Modules.Invertible
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [h_L : Scheme.Modules.Invertible ((Scheme.Modules.pullback f).obj L)]
    (C : Scheme.TensorSectionSplitting
      ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ Scheme.zeroScheme ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ Scheme.zeroSchemeι ((Scheme.Modules.pullback f).obj L)
      (Scheme.Modules.sectionsPullback f L s) = C.baseι)
    (k : ℤ) (alpha : RelativeChow delta (Over.mk (f ≫ X.hom)) k) :
    @firstGysin S inferInstance delta inferInstance (Over.mk (f ≫ X.hom))
        inferInstance ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
        ((Scheme.Modules.pullback f).obj L) h_unit h_L
        (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s)) C k
        (@projectionPullback S inferInstance delta inferInstance (Over.mk (f ≫ X.hom))
          inferInstance ((Scheme.Modules.pullback f).obj (𝟙_ X.left.Modules))
          ((Scheme.Modules.pullback f).obj L) h_unit h_L
          (Scheme.Modules.pullbackTensorSection f (Scheme.Modules.unitTensorSection L s))
          C k alpha) =
      pullbackUnitProjectionPullback delta X L s f C e h_e k
        (@ChowGroup.gysin S inferInstance delta inferInstance (Over.mk (f ≫ X.hom))
          inferInstance ((Scheme.Modules.pullback f).obj L) h_L
          (Scheme.Modules.sectionsPullback f L s) k alpha) := sorry

/-- The transported first-projection pullback is injective in every degree. -/
theorem unitProjectionPullback_injective
    (e : C.baseZero ≅ Scheme.zeroScheme L s)
    (h_e : e.hom ≫ Scheme.zeroSchemeι L s = C.baseι) (k : ℤ) :
    Function.Injective (unitProjectionPullback delta X L s C e h_e k) := sorry

/-- First-factor Gysin pullback commutes with projection pullback after transport
to the zero scheme of the original section. -/
theorem gysin_unitProjectionPullback
    (e : C.baseZero ≅ Scheme.zeroScheme L s)
    (h_e : e.hom ≫ Scheme.zeroSchemeι L s = C.baseι)
    (k : ℤ) (alpha : RelativeChow delta X k) :
    firstGysin delta X C k (projectionPullback delta X C k alpha) =
      unitProjectionPullback delta X L s C e h_e k
        (ChowGroup.gysin delta X L s k alpha) := sorry

end AlgebraicGeometry.ChowGroup.TensorSectionSplitting
