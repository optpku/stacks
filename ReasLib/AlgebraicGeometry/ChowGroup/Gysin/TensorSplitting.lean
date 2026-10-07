module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting.Over

/-!
# Chow maps for tensor-section splittings

This file defines the four Chow operations associated to a tensor-section
splitting and states their compatibility.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.TensorSectionSplitting

open Scheme.TensorSectionSplitting

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (delta : S → ℤ) [IsDimensionFunction delta]
variable (Y : Over S) [LocallyOfFiniteType Y.hom]
variable {L₁ L₂ : Y.left.Modules}
variable [Scheme.Modules.Invertible L₁] [Scheme.Modules.Invertible L₂]
variable {s : (L₁ ⊗ L₂).sections} (C : Scheme.TensorSectionSplitting L₁ L₂ s)

/-- The first factor zero scheme is locally noetherian under the ambient finite-type
hypothesis. -/
theorem zero₁Over_isLocallyNoetherian : IsLocallyNoetherian (zero₁Over Y C).left := sorry

/-- The grading induced on the first factor zero scheme is a dimension function. -/
theorem zero₁Over_isDimensionFunction :
    IsDimensionFunction ((zero₁Over Y C).hom.relativeDimensionFunction delta) := sorry

/-- The first line model is locally noetherian under the ambient finite-type hypothesis. -/
theorem lineModel₁Over_isLocallyNoetherian :
    IsLocallyNoetherian (lineModel₁Over Y C).left := sorry

/-- The grading induced on the first line model is a dimension function. -/
theorem lineModel₁Over_isDimensionFunction :
    IsDimensionFunction ((lineModel₁Over Y C).hom.relativeDimensionFunction delta) := sorry

/-- Flat pullback along the splitting projection. -/
noncomputable def projectionPullback (k : ℤ) :
    RelativeChow delta Y k →+
      @RelativeChow S inferInstance delta inferInstance (totalOver Y C)
        (totalOver_locallyOfFiniteType Y C) (k + 1) :=
  @ChowGroup.flatPullback S inferInstance delta inferInstance
    (totalOver Y C) Y (totalOver_locallyOfFiniteType Y C) inferInstance
    (Over.homMk C.p) 1 C.projection_flat C.projection_relativeDimension k

/-- `projectionPullback` is the canonical degree-one flat pullback along `C.p`. -/
theorem projectionPullback_def (k : ℤ) :
    projectionPullback delta Y C k =
      @ChowGroup.flatPullback S inferInstance delta inferInstance
        (totalOver Y C) Y (totalOver_locallyOfFiniteType Y C) inferInstance
        (Over.homMk C.p) 1 C.projection_flat C.projection_relativeDimension k := sorry

/-- Gysin pullback along the zero scheme of the original tensor-product section. -/
noncomputable def baseGysin (k : ℤ) :
    RelativeChow delta Y k →+
      @RelativeChow S inferInstance delta inferInstance (baseZeroOver Y C)
        (baseZeroOver_locallyOfFiniteType Y C) (k - 1) :=
  ChowGroup.gysin delta Y (L₁ ⊗ L₂) s k

/-- `baseGysin` is the canonical Gysin pullback for the tensor-product section. -/
theorem baseGysin_def (k : ℤ) :
    baseGysin delta Y C k = ChowGroup.gysin delta Y (L₁ ⊗ L₂) s k := sorry

/-- Gysin pullback along the first factor zero scheme, normalized to degree `k`. -/
noncomputable def firstGysin (k : ℤ) :
    @RelativeChow S inferInstance delta inferInstance (totalOver Y C)
        (totalOver_locallyOfFiniteType Y C) (k + 1) →+
      @RelativeChow S inferInstance delta inferInstance (zero₁Over Y C)
        (zero₁Over_locallyOfFiniteType Y C) k :=
  (@ChowGroup.reindex (zero₁Over Y C).left
      (zero₁Over_isLocallyNoetherian Y C)
      ((zero₁Over Y C).hom.relativeDimensionFunction delta)
      (zero₁Over_isDimensionFunction delta Y C)
      ((k + 1) - 1) k (add_sub_cancel_right k 1)).toAddMonoidHom.comp
    (@ChowGroup.gysin S inferInstance delta inferInstance (totalOver Y C)
      (totalOver_locallyOfFiniteType Y C) ((Scheme.Modules.pullback C.p).obj L₁)
      (Scheme.Modules.Invertible.pullback C.p inferInstance) C.s₁ (k + 1))

/-- `firstGysin` is the first-factor Gysin map followed by canonical grade transport. -/
theorem firstGysin_def (k : ℤ) :
    firstGysin delta Y C k =
      (@ChowGroup.reindex (zero₁Over Y C).left
        (zero₁Over_isLocallyNoetherian Y C)
        ((zero₁Over Y C).hom.relativeDimensionFunction delta)
        (zero₁Over_isDimensionFunction delta Y C)
        ((k + 1) - 1) k (add_sub_cancel_right k 1)).toAddMonoidHom.comp
      (@ChowGroup.gysin S inferInstance delta inferInstance (totalOver Y C)
        (totalOver_locallyOfFiniteType Y C) ((Scheme.Modules.pullback C.p).obj L₁)
        (Scheme.Modules.Invertible.pullback C.p inferInstance) C.s₁ (k + 1)) := sorry

/-- Flat pullback along the first line-model projection, transported to the first zero
scheme and normalized to degree `k`. -/
noncomputable def firstProjectionPullback (k : ℤ) :
    @RelativeChow S inferInstance delta inferInstance (baseZeroOver Y C)
        (baseZeroOver_locallyOfFiniteType Y C) (k - 1) →+
      @RelativeChow S inferInstance delta inferInstance (zero₁Over Y C)
        (zero₁Over_locallyOfFiniteType Y C) k :=
  (@ChowGroup.map S inferInstance delta inferInstance
      (lineModel₁Over Y C) (zero₁Over Y C)
      (lineModel₁Over_locallyOfFiniteType Y C) (zero₁Over_locallyOfFiniteType Y C)
      (lineIso₁Over Y C).inv (lineIso₁Over_inv_isProper Y C) k).comp
    ((@ChowGroup.reindex (lineModel₁Over Y C).left
        (lineModel₁Over_isLocallyNoetherian Y C)
        ((lineModel₁Over Y C).hom.relativeDimensionFunction delta)
        (lineModel₁Over_isDimensionFunction delta Y C)
        ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
      (@ChowGroup.flatPullback S inferInstance delta inferInstance
        (lineModel₁Over Y C) (baseZeroOver Y C)
        (lineModel₁Over_locallyOfFiniteType Y C) (baseZeroOver_locallyOfFiniteType Y C)
        (Over.homMk C.lineModel₁.π) 1 (lineModel₁Projection_flat Y C)
        (lineModel₁Projection_relativeDimension Y C) (k - 1)))

/-- `firstProjectionPullback` is line-model flat pullback, grade normalization, and
proper transport through `lineIso₁Over.symm`. -/
theorem firstProjectionPullback_def (k : ℤ) :
    firstProjectionPullback delta Y C k =
      (@ChowGroup.map S inferInstance delta inferInstance
        (lineModel₁Over Y C) (zero₁Over Y C)
        (lineModel₁Over_locallyOfFiniteType Y C) (zero₁Over_locallyOfFiniteType Y C)
        (lineIso₁Over Y C).inv (lineIso₁Over_inv_isProper Y C) k).comp
      ((@ChowGroup.reindex (lineModel₁Over Y C).left
          (lineModel₁Over_isLocallyNoetherian Y C)
          ((lineModel₁Over Y C).hom.relativeDimensionFunction delta)
          (lineModel₁Over_isDimensionFunction delta Y C)
          ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
        (@ChowGroup.flatPullback S inferInstance delta inferInstance
          (lineModel₁Over Y C) (baseZeroOver Y C)
          (lineModel₁Over_locallyOfFiniteType Y C) (baseZeroOver_locallyOfFiniteType Y C)
          (Over.homMk C.lineModel₁.π) 1 (lineModel₁Projection_flat Y C)
          (lineModel₁Projection_relativeDimension Y C) (k - 1))) := sorry

/-- Gysin pullback along the first zero scheme after pullback along the splitting
projection equals pullback along the first line model after Gysin pullback along the
tensor-product zero scheme. -/
theorem gysin_flatPullback (k : ℤ) (alpha : RelativeChow delta Y k) :
    firstGysin delta Y C k (projectionPullback delta Y C k alpha) =
      firstProjectionPullback delta Y C k (baseGysin delta Y C k alpha) := sorry

end AlgebraicGeometry.ChowGroup.TensorSectionSplitting
