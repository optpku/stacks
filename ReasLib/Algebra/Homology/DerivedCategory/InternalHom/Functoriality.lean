module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of derived internal Hom

@stack 0BYN
@stack 0A65
@stack 0A67
@stack 0A8J
@stack 0A6B
@stack 0A8W

The generic closed-monoidal leaves own two-variable internal-Hom maps, parametrized adjunctions,
and composition.  This file gives their short module-derived-category spellings.  An explicit
fixed-right tensor model transports canonical derived tensoring to the ambient tensor; it stays
visible because a closed structure alone does not determine that comparison.

The module facade follows Mathlib's same-universe `ModuleCat` monoidal instance.  The generic
closed and derived-tensor owners imported below remain category- and universe-polymorphic.
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped _root_.DerivedInternalHom CategoryTheory.DerivedCategory.DerivedTensor

namespace CategoryTheory.DerivedCategory.InternalHom

variable {A : Type u} [CommRing A]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- The map of selected derived internal-Hom objects, contravariant in the source and covariant
in the target, with the closed owner supplied explicitly. -/
@[stacks 0E1U "derived internal-Hom map from an explicit owner"]
noncomputable abbrev mapOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{u} A)}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    RHom[H](K₁, L₁) ⟶ RHom[H](K₂, L₂) :=
  MonoidalClosed.internalHomMapOf H fK fL

/-- The canonical fixed-right derived tensor adjunction obtained from an explicit closed owner
and an explicit ambient-to-derived tensor model. -/
@[stacks 064M "derived tensor adjunction from explicit owners"]
noncomputable abbrev adjunctionOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (L : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.functor L ⊣ MonoidalClosed.ihomOf H L :=
  DerivedTensor.Right.Closed.adjunctionOf H T L

/-- The natural transformation between fixed-right derived tensor functors induced by a map of
right factors.  It is the canonical left mate for `adjunctionOf H T`. -/
@[stacks 064M "derived tensor parameter map from explicit owners"]
noncomputable abbrev tensorMapOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.functor L₁ ⟶ DerivedTensor.Right.functor L₂ :=
  DerivedTensor.Right.Closed.tensorMapOf H T f

/-- The mate-generated module-derived tensor parameter map is ambient right tensoring transported
through the explicit model comparisons. -/
@[reassoc, stacks 064M "module derived tensor parameter map comparison"]
theorem tensorMapOf_objIsoTensor
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (tensorMapOf H T f).app K ≫
          (DerivedTensor.Right.Monoidal.Model.objIsoTensor T K L₂).hom =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor T K L₁).hom ≫
        (𝟙 K ⊗ₘ f) :=
  DerivedTensor.Right.Closed.tensorMapOf_objIsoTensor H T f K

namespace TensorLeft

/-- Stacks 0BYN: the canonical tensor-left/internal-Hom comparison in module-derived notation.
The explicit tensor model keeps the transport from `⊗ᴸ` to the ambient closed tensor visible. -/
@[stacks 0BYN "module derived tensor/internal-Hom comparison"]
noncomputable abbrev comparisonOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.obj K (RHom[H](M, L)) ⟶
      RHom[H](M, DerivedTensor.Right.obj K L) :=
  DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf H T K L M

/-- The module-derived tensor/internal-Hom comparison is natural in its tensor factor. -/
@[stacks 0BYN "module derived tensor/internal-Hom tensor naturality"]
theorem comparisonOf_natural_tensor
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {K₁ K₂ L M : DerivedCategory (ModuleCat.{u} A)} (fK : K₁ ⟶ K₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((DerivedTensor.Right.functor (RHom[H](M, L))).map fK)
      (comparisonOf H T K₁ L M)
      (comparisonOf H T K₂ L M)
      (mapOf H (𝟙 M) ((DerivedTensor.Right.functor L).map fK)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf_natural_tensor H T fK

/-- The module-derived tensor/internal-Hom comparison is natural in the internal-Hom target. -/
@[stacks 0BYN "module derived tensor/internal-Hom target naturality"]
theorem comparisonOf_natural_target
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K M : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (fL : L₁ ⟶ L₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((tensorMapOf H T (mapOf H (𝟙 M) fL)).app K)
      (comparisonOf H T K L₁ M)
      (comparisonOf H T K L₂ M)
      (mapOf H (𝟙 M) ((tensorMapOf H T fL).app K)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf_natural_target H T K M fL

/-- The module-derived tensor/internal-Hom comparison is contravariantly natural in its
internal-Hom source. -/
@[stacks 0BYN "module derived tensor/internal-Hom source naturality"]
theorem comparisonOf_natural_source
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    {M₁ M₂ : DerivedCategory (ModuleCat.{u} A)} (fM : M₁ ⟶ M₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((tensorMapOf H T (mapOf H fM (𝟙 L))).app K)
      (comparisonOf H T K L M₂)
      (comparisonOf H T K L M₁)
      (mapOf H fM (𝟙 (DerivedTensor.Right.obj K L))) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre] using
    DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf_natural_source H T K L fM

end TensorLeft

namespace TensorSource

/-- 0A65: the iterated derived internal-Hom isomorphism in module-derived notation.  The explicit
closed owner and tensor model make the comparison with `⊗ᴸ` canonical for downstream use. -/
@[stacks 0A65, stacks 01CN, stacks 03EO, stacks 08DJ "module derived internal-Hom tensor-source isomorphism"]
noncomputable abbrev isoOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    RHom[H](K, RHom[H](L, M)) ≅ RHom[H](DerivedTensor.Right.obj K L, M) :=
  DerivedTensor.Right.Closed.InternalHomTensor.isoOf H T K L M

/-- The module-derived iterated internal-Hom isomorphism is contravariantly natural in its left
factor. -/
@[stacks 03EO "module derived internal-Hom tensor-source left naturality"]
theorem isoOf_natural_left
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {K₁ K₂ L M : DerivedCategory (ModuleCat.{u} A)} (f : K₁ ⟶ K₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    mapOf H f (𝟙 (RHom[H](L, M))) ≫ (isoOf H T K₁ L M).hom =
      (isoOf H T K₂ L M).hom ≫
        mapOf H ((DerivedTensor.Right.functor L).map f) (𝟙 M) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre] using
    DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_left H T f

/-- The module-derived iterated internal-Hom isomorphism is contravariantly natural in its middle
factor. -/
@[stacks 03EO "module derived internal-Hom tensor-source middle naturality"]
theorem isoOf_natural_middle
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ M : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    mapOf H (𝟙 K) (mapOf H f (𝟙 M)) ≫ (isoOf H T K L₁ M).hom =
      (isoOf H T K L₂ M).hom ≫
        mapOf H ((tensorMapOf H T f).app K) (𝟙 M) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre,
    MonoidalClosed.internalHomMapOf_post] using
      DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_middle H T K f

/-- The module-derived iterated internal-Hom isomorphism is covariantly natural in its target. -/
@[stacks 03EO "module derived internal-Hom tensor-source target naturality"]
theorem isoOf_natural_right
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    {M₁ M₂ : DerivedCategory (ModuleCat.{u} A)} (f : M₁ ⟶ M₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    mapOf H (𝟙 K) (mapOf H (𝟙 L) f) ≫ (isoOf H T K L M₂).hom =
      (isoOf H T K L M₁).hom ≫
        mapOf H (𝟙 (DerivedTensor.Right.obj K L)) f := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.InternalHomTensor.isoOf_natural_right H T K L f

end TensorSource

namespace TensorRight

/-- Stacks 0A67, 0A8U, and 0A92: the source-order tensor-to-iterated internal-Hom comparison in
module-derived notation.  The explicit model transports the fixed-right derived tensor source to
ambient tensoring. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92 "module derived tensor-to-iterated internal-Hom comparison"]
noncomputable abbrev comparisonOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.obj (RHom[H](L, M)) K ⟶ RHom[H](RHom[H](K, L), M) :=
  DerivedTensor.Right.Closed.TensorRight.comparisonOf H T K L M

/-- The module-derived tensor-to-iterated comparison is ambient closed composition transported
through the tensor-model isomorphism. -/
@[stacks 0A8U "module derived tensor-to-iterated comparison specification"]
theorem comparisonOf_spec
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    comparisonOf H T K L M =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor T (RHom[H](L, M)) K).hom ≫
        MonoidalClosed.TensorRight.comparisonOf H K L M :=
  DerivedTensor.Right.Closed.TensorRight.comparisonOf_spec H T K L M

/-- The module-derived tensor-to-iterated comparison is natural in its fixed tensor parameter. -/
@[stacks 0A8U "module derived tensor-to-iterated tensor naturality"]
theorem comparisonOf_natural_tensor
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {K₁ K₂ L M : DerivedCategory (ModuleCat.{u} A)} (fK : K₁ ⟶ K₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((tensorMapOf H T fK).app (RHom[H](L, M)))
      (comparisonOf H T K₁ L M)
      (comparisonOf H T K₂ L M)
      (mapOf H (mapOf H fK (𝟙 L)) (𝟙 M)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre] using
    DerivedTensor.Right.Closed.TensorRight.comparisonOf_natural_tensor H T fK

/-- The module-derived tensor-to-iterated comparison is contravariantly natural in its middle
object. -/
@[stacks 0A8U "module derived tensor-to-iterated middle naturality"]
theorem comparisonOf_natural_middle
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ M : DerivedCategory (ModuleCat.{u} A)} (fL : L₁ ⟶ L₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((DerivedTensor.Right.functor K).map (mapOf H fL (𝟙 M)))
      (comparisonOf H T K L₂ M)
      (comparisonOf H T K L₁ M)
      (mapOf H (mapOf H (𝟙 K) fL) (𝟙 M)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre,
    MonoidalClosed.internalHomMapOf_post] using
      DerivedTensor.Right.Closed.TensorRight.comparisonOf_natural_middle H T K fL

/-- The module-derived tensor-to-iterated comparison is covariantly natural in its target. -/
@[stacks 0A8U "module derived tensor-to-iterated target naturality"]
theorem comparisonOf_natural_target
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    {M₁ M₂ : DerivedCategory (ModuleCat.{u} A)} (fM : M₁ ⟶ M₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((DerivedTensor.Right.functor K).map (mapOf H (𝟙 L) fM))
      (comparisonOf H T K L M₁)
      (comparisonOf H T K L M₂)
      (mapOf H (𝟙 (RHom[H](K, L))) fM) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.TensorRight.comparisonOf_natural_target H T K L fM

end TensorRight

/-- Stacks 0A8J: composition of derived internal-Hom objects, with the canonical derived tensor
as source.  The explicit model records the comparison with the ambient tensor of `H`; no global
monoidal localization or proof-local instance is hidden by this interface. -/
@[stacks 0A8J "derived internal-Hom composition"]
noncomputable abbrev compOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    (RHom[H](L, M)) ⊗ᴸ (RHom[H](K, L)) ⟶ RHom[H](K, M) :=
  DerivedTensor.Right.Closed.compOf H T K L M

/-- The selected derived internal-Hom composition is natural in its target object. -/
@[stacks 0A8J "module derived internal-Hom composition target naturality"]
theorem compOf_natural_target
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    {M₁ M₂ : DerivedCategory (ModuleCat.{u} A)} (f : M₁ ⟶ M₂) :
    CommSq
      ((DerivedTensor.Right.functor (RHom[H](K, L))).map (mapOf H (𝟙 L) f))
      (compOf H T K L M₁)
      (compOf H T K L M₂)
      (mapOf H (𝟙 K) f) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.compOf_natural_target H T K L f

/-- The selected derived internal-Hom composition is contravariantly natural in its source
object. -/
@[stacks 0A8J "module derived internal-Hom composition source naturality"]
theorem compOf_natural_source
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₁ ⟶ K₂)
    (L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((tensorMapOf H T (mapOf H f (𝟙 L))).app (RHom[H](L, M)))
      (compOf H T K₂ L M)
      (compOf H T K₁ L M)
      (mapOf H f (𝟙 M)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre] using
    DerivedTensor.Right.Closed.compOf_natural_source H T f L M

/-- The selected derived internal-Hom composition has the expected opposite variances in its
middle object. -/
@[stacks 0A8J "module derived internal-Hom composition middle naturality"]
theorem compOf_natural_middle
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (g : L₁ ⟶ L₂)
    (M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((DerivedTensor.Right.functor (RHom[H](K, L₁))).map (mapOf H g (𝟙 M)))
      ((tensorMapOf H T (mapOf H (𝟙 K) g)).app (RHom[H](L₂, M)))
      (compOf H T K L₁ M)
      (compOf H T K L₂ M) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre,
    MonoidalClosed.internalHomMapOf_post] using
      DerivedTensor.Right.Closed.compOf_natural_middle H T K g M

/-- Stacks `0A6B` and `0A8W`: the unit of the selected derived tensor/internal-Hom adjunction, in
module-derived notation.  This is the reusable owner of the canonical map
`K ⟶ RHom[H](L, K ⊗ᴸ L)`. -/
@[stacks 0A6B, stacks 0A8W "module derived tensor/internal-Hom unit"]
noncomputable abbrev unitOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    K ⟶ RHom[H](L, DerivedTensor.Right.obj K L) :=
  DerivedTensor.Right.Closed.unitOf H T K L

/-- Stacks `0A8W`: the module-derived evaluation map selected by an explicit closed owner and
tensor model. -/
@[stacks 0A8W "module derived tensor/internal-Hom counit"]
noncomputable abbrev counitOf
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (E N : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.obj (RHom[H](E, N)) E ⟶ N :=
  DerivedTensor.Right.Closed.counitOf H T E N

/-- The selected module-derived adjunction unit is natural in its source object. -/
@[reassoc, stacks 0A6B, stacks 0A8W "module derived tensor/internal-Hom unit naturality"]
theorem unitOf_natural_left
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (L : DerivedCategory (ModuleCat.{u} A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₁ ⟶ K₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    f ≫ unitOf H T K₂ L =
      unitOf H T K₁ L ≫ mapOf H (𝟙 L) ((DerivedTensor.Right.functor L).map f) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.unitOf_natural_left H T L f

/-- The selected module-derived adjunction unit is naturally compatible with changing its right
tensor factor. -/
@[stacks 0A6B, stacks 0A8W "module derived tensor/internal-Hom unit parameter naturality"]
theorem unitOf_natural_right
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      (unitOf H T K L₂)
      (unitOf H T K L₁)
      (mapOf H f (𝟙 (DerivedTensor.Right.obj K L₂)))
      (mapOf H (𝟙 L₁) ((tensorMapOf H T f).app K)) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre,
    MonoidalClosed.internalHomMapOf_post] using
      DerivedTensor.Right.Closed.unitOf_natural_right H T K f

/-- The selected module-derived adjunction counit is natural in its target object. -/
@[reassoc, stacks 0A8W "module derived tensor/internal-Hom counit naturality"]
theorem counitOf_natural_target
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (E : DerivedCategory (ModuleCat.{u} A))
    {N₁ N₂ : DerivedCategory (ModuleCat.{u} A)} (f : N₁ ⟶ N₂)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    (DerivedTensor.Right.functor E).map (mapOf H (𝟙 E) f) ≫
        counitOf H T E N₂ =
      counitOf H T E N₁ ≫ f := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_post] using
    DerivedTensor.Right.Closed.counitOf_natural_target H T E f

/-- The selected module-derived adjunction counit is naturally compatible with changing its
right tensor factor. -/
@[stacks 0A8W "module derived tensor/internal-Hom counit parameter naturality"]
theorem counitOf_natural_source
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    {E₁ E₂ : DerivedCategory (ModuleCat.{u} A)} (f : E₁ ⟶ E₂)
    (N : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    CommSq
      ((tensorMapOf H T f).app (RHom[H](E₂, N)))
      ((DerivedTensor.Right.functor E₁).map (mapOf H f (𝟙 N)))
      (counitOf H T E₂ N)
      (counitOf H T E₁ N) := by
  simpa only [mapOf, MonoidalClosed.internalHomMapOf_pre] using
    DerivedTensor.Right.Closed.counitOf_natural_source H T f N

end CategoryTheory.DerivedCategory.InternalHom
