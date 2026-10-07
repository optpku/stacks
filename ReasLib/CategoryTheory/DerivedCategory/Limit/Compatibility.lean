module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Transport
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Compatibility for Legacy and Explicit Homotopy Limits

@stack 08TC

This leaf relates the legacy `IsDerivedLimit`, which stores a `HasProduct` witness, to the neutral
`HomotopyLimit.Presentation` and `HomotopyLimit.IsOf` APIs, which retain an explicit product cone.

The local `letI` expressions below are deliberately confined to this compatibility boundary. They
only reinstall a `HasProduct` stored by the legacy structure, or temporarily install the
`HasProduct` canonically supplied by an explicit `LimitCone`. The neutral presentation API itself
does not depend on these ambient instances, and no presentation-dependent instance is registered
globally.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace IsDerivedLimit

/-- The explicit product cone selected by the product witness stored in a legacy derived-limit
presentation. -/
def canonicalProduct {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : LimitCone (Discrete.functor K.family) :=
  letI := h.hasProduct
  getLimitCone (Discrete.functor K.family)

/-- The inclusion of a legacy derived-limit witness into its explicitly retained canonical
product cone. -/
def canonicalInclusion {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : X ⟶ h.canonicalProduct.cone.pt :=
  letI := h.hasProduct
  h.milnor.ι

/-- The connecting morphism of a legacy derived-limit witness, with its canonical product cone
made explicit. -/
def canonicalConnecting {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : h.canonicalProduct.cone.pt ⟶ X⟦(1 : ℤ)⟧ :=
  letI := h.hasProduct
  h.milnor.δ

/-- The explicit-cone Milnor triangle extracted from a legacy derived-limit witness is
distinguished. -/
@[stacks 08TC]
theorem canonical_mem_distTriang {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) :
    Triangle.mk h.canonicalInclusion
      (SequentialInverseSystem.Milnor.ProductCone.difference K h.canonicalProduct)
      h.canonicalConnecting ∈ distTriang D := sorry

/-- Stacks 08TC: the canonical explicit homotopy-limit presentation underlying a legacy
`IsDerivedLimit` witness. -/
@[stacks 08TC]
def toPresentation {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : HomotopyLimit.Presentation K X where
  product := h.canonicalProduct
  ι := h.canonicalInclusion
  connecting := h.canonicalConnecting
  distinguished := h.canonical_mem_distTriang

/-- The product stored by the explicit presentation of a legacy witness is its canonical
product cone. -/
@[simp]
theorem toPresentation_product {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) :
    h.toPresentation.product = h.canonicalProduct := sorry

/-- Passing a legacy derived-limit witness to an explicit presentation preserves every stage
projection. -/
@[simp, stacks 08TC]
theorem toPresentation_stageProjection {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) (n : ℕ) :
    h.toPresentation.stageProjection n = h.stageProjection n := sorry

/-- A legacy derived-limit witness determines the neutral, presentation-independent
homotopy-limit predicate. -/
@[stacks 08TC]
theorem toIsOf {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : HomotopyLimit.IsOf K X := sorry

end IsDerivedLimit

namespace HomotopyLimit.Presentation

/-- The product-existence witness supplied by the explicit product cone of a presentation.
This witness is intentionally not registered as an instance. -/
abbrev hasProduct {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : HasProduct K.family :=
  HasLimit.mk P.product

/-- The presentation transported along the identity tower isomorphism to the canonical product
selected by `P.hasProduct`. -/
@[stacks 08TC]
def canonicalPresentation {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : Presentation K X :=
  letI := P.hasProduct
  P.ofTowerIso (CategoryTheory.Iso.refl K) (getLimitCone (Discrete.functor K.family))

/-- The identity-transported presentation stores the product cone selected by `P.hasProduct`. -/
@[simp]
theorem canonicalPresentation_product {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    letI := P.hasProduct
    P.canonicalPresentation.product = getLimitCone (Discrete.functor K.family) := sorry

/-- Transport to the product selected by `P.hasProduct` preserves every stage projection. -/
@[simp, stacks 08TC]
theorem canonicalPresentation_stageProjection
    {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.canonicalPresentation.stageProjection n = P.stageProjection n := sorry

/-- The canonical presentation associated to `P.hasProduct` is distinguished when its explicit
difference is written as the legacy `milnorDifferenceMap`. -/
@[stacks 08TC]
theorem canonicalPresentation_mem_distTriang
    {K : SequentialInverseSystem D} {X : D} (P : Presentation K X) :
    letI := P.hasProduct
    Triangle.mk P.canonicalPresentation.ι K.milnorDifferenceMap
      P.canonicalPresentation.connecting ∈ distTriang D := sorry

/-- The legacy Milnor triangle obtained from the canonical presentation associated to
`P.hasProduct`. -/
@[stacks 08TC]
def toMilnorTriangle {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    letI := P.hasProduct
    HasMilnorTriangle K X :=
  letI := P.hasProduct
  { ι := P.canonicalPresentation.ι
    δ := P.canonicalPresentation.connecting
    mem_distTriang := P.canonicalPresentation_mem_distTriang }

/-- Stacks 08TC: an explicit homotopy-limit presentation determines a legacy
`IsDerivedLimit` witness without making a presentation-dependent product instance global. -/
@[stacks 08TC]
def toIsDerivedLimit {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : IsDerivedLimit K X where
  hasProduct := P.hasProduct
  milnor := letI := P.hasProduct; P.toMilnorTriangle

/-- Passing an explicit presentation to the legacy derived-limit structure preserves every
stage projection. -/
@[simp, stacks 08TC]
theorem toIsDerivedLimit_stageProjection
    {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.toIsDerivedLimit.stageProjection n = P.stageProjection n := sorry

end HomotopyLimit.Presentation

namespace HomotopyLimit

/-- Stacks 08TC: existence of a legacy derived-limit witness is equivalent to the neutral
presentation-independent homotopy-limit predicate. -/
@[stacks 08TC]
theorem nonempty_isDerivedLimit_iff_isOf
    {K : SequentialInverseSystem D} {X : D} :
    Nonempty (IsDerivedLimit K X) ↔ HomotopyLimit.IsOf K X := sorry

end HomotopyLimit

end CategoryTheory
