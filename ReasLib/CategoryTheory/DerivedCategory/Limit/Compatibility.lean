/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

private theorem compatibility_difference_comp_projection {D : Type u} [Category.{v} D]
    [Preadditive D] (K : SequentialInverseSystem D)
    (P : LimitCone (Discrete.functor K.family)) (n : ℕ) :
    SequentialInverseSystem.Milnor.ProductCone.difference K P ≫
        SequentialInverseSystem.Milnor.ProductCone.projection P n =
      SequentialInverseSystem.Milnor.ProductCone.projection P n -
        SequentialInverseSystem.Milnor.ProductCone.projection P (n + 1) ≫
          K.transitionMap (Nat.le_succ n) :=
  P.isLimit.fac _ ⟨n⟩

private theorem compatibility_map_comp_projection {D : Type u} [Category.{v} D]
    {K L : SequentialInverseSystem D}
    (P : LimitCone (Discrete.functor K.family)) (Q : LimitCone (Discrete.functor L.family))
    (f : K ⟶ L) (n : ℕ) :
    SequentialInverseSystem.Milnor.ProductCone.map P Q f ≫
        SequentialInverseSystem.Milnor.ProductCone.projection Q n =
      SequentialInverseSystem.Milnor.ProductCone.projection P n ≫ f.app (op n) :=
  Q.isLimit.fac _ ⟨n⟩

private theorem compatibility_difference_getLimitCone {D : Type u} [Category.{v} D]
    [Preadditive D] (K : SequentialInverseSystem D)
    [HasProduct K.family] :
    SequentialInverseSystem.Milnor.ProductCone.difference K
      (getLimitCone (Discrete.functor K.family)) = K.milnorDifferenceMap := by
  change Pi.lift (fun n ↦ Pi.π K.family n -
    Pi.π K.family (n + 1) ≫ K.transitionMap (Nat.le_succ n)) = K.milnorDifferenceMap
  apply Pi.hom_ext
  intro n
  rw [Pi.lift_π]
  simp only [SequentialInverseSystem.milnorDifferenceMap, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π]

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
      h.canonicalConnecting ∈ distTriang D := by
  letI := h.hasProduct
  change Triangle.mk h.milnor.ι
    (SequentialInverseSystem.Milnor.ProductCone.difference K
      (getLimitCone (Discrete.functor K.family))) h.milnor.δ ∈ distTriang D
  rw [compatibility_difference_getLimitCone]
  exact h.milnor.mem_distTriang

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
    h.toPresentation.product = h.canonicalProduct := rfl

/-- Passing a legacy derived-limit witness to an explicit presentation preserves every stage
projection. -/
@[simp, stacks 08TC]
theorem toPresentation_stageProjection {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) (n : ℕ) :
    h.toPresentation.stageProjection n = h.stageProjection n := rfl

/-- A legacy derived-limit witness determines the neutral, presentation-independent
homotopy-limit predicate. -/
@[stacks 08TC]
theorem toIsOf {K : SequentialInverseSystem D} {X : D}
    (h : IsDerivedLimit K X) : HomotopyLimit.IsOf K X :=
  ⟨h.canonicalProduct, h.canonicalInclusion, h.canonicalConnecting, h.canonical_mem_distTriang⟩

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
    P.canonicalPresentation.product = getLimitCone (Discrete.functor K.family) := by
  letI := P.hasProduct
  change getLimitCone (Discrete.functor K.family) = getLimitCone (Discrete.functor K.family)
  rfl

/-- Transport to the product selected by `P.hasProduct` preserves every stage projection. -/
@[simp, stacks 08TC]
theorem canonicalPresentation_stageProjection
    {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.canonicalPresentation.stageProjection n = P.stageProjection n := by
  letI := P.hasProduct
  change (P.ι ≫ Pi.lift (f := K.family)
    (fun m ↦ SequentialInverseSystem.Milnor.ProductCone.projection P.product m ≫ 𝟙 _)) ≫
    Pi.π K.family n = P.ι ≫ SequentialInverseSystem.Milnor.ProductCone.projection P.product n
  simp only [Category.assoc, Pi.lift_π, Category.comp_id]

private theorem compatibility_changeProduct_distinguished
    {K : SequentialInverseSystem D} {X : D} (P : Presentation K X)
    (Q : LimitCone (Discrete.functor K.family)) :
    Triangle.mk (P.ι ≫ SequentialInverseSystem.Milnor.ProductCone.map P.product Q (𝟙 K))
      (SequentialInverseSystem.Milnor.ProductCone.difference K Q)
      (SequentialInverseSystem.Milnor.ProductCone.map Q P.product (𝟙 K) ≫ P.connecting) ∈
        distTriang D := by
  let e := P.product.isLimit.conePointUniqueUpToIso Q.isLimit
  have hmap : SequentialInverseSystem.Milnor.ProductCone.map P.product Q (𝟙 K) =
      e.hom := by
    apply Q.isLimit.hom_ext
    intro ⟨n⟩
    change SequentialInverseSystem.Milnor.ProductCone.map P.product Q (𝟙 K) ≫
        SequentialInverseSystem.Milnor.ProductCone.projection Q n =
      e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.projection Q n
    rw [compatibility_map_comp_projection, NatTrans.id_app, Category.comp_id]
    exact (P.product.isLimit.conePointUniqueUpToIso_hom_comp Q.isLimit ⟨n⟩).symm
  have hmapInv : SequentialInverseSystem.Milnor.ProductCone.map Q P.product (𝟙 K) =
      e.inv := by
    apply P.product.isLimit.hom_ext
    intro ⟨n⟩
    change SequentialInverseSystem.Milnor.ProductCone.map Q P.product (𝟙 K) ≫
        SequentialInverseSystem.Milnor.ProductCone.projection P.product n =
      e.inv ≫ SequentialInverseSystem.Milnor.ProductCone.projection P.product n
    rw [compatibility_map_comp_projection, NatTrans.id_app, Category.comp_id]
    exact (P.product.isLimit.conePointUniqueUpToIso_inv_comp Q.isLimit ⟨n⟩).symm
  have hcomm : SequentialInverseSystem.Milnor.ProductCone.difference K P.product ≫ e.hom =
      e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.difference K Q := by
    have he (n : ℕ) : e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.projection Q n =
        SequentialInverseSystem.Milnor.ProductCone.projection P.product n :=
      P.product.isLimit.conePointUniqueUpToIso_hom_comp Q.isLimit ⟨n⟩
    apply Q.isLimit.hom_ext
    intro ⟨n⟩
    change (SequentialInverseSystem.Milnor.ProductCone.difference K P.product ≫ e.hom) ≫
        SequentialInverseSystem.Milnor.ProductCone.projection Q n =
      (e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.difference K Q) ≫
        SequentialInverseSystem.Milnor.ProductCone.projection Q n
    rw [Category.assoc, he, Category.assoc, compatibility_difference_comp_projection,
      compatibility_difference_comp_projection, Preadditive.comp_sub, ← Category.assoc, he, he]
  have hdist : Triangle.mk (P.ι ≫ e.hom)
      (SequentialInverseSystem.Milnor.ProductCone.difference K Q)
      (e.inv ≫ P.connecting) ∈ distTriang D := by
    apply isomorphic_distinguished _ P.distinguished _
    refine (Triangle.isoMk _ _ (CategoryTheory.Iso.refl X) e e ?_ hcomm ?_).symm
    · change P.ι ≫ e.hom = 𝟙 X ≫ (P.ι ≫ e.hom)
      rw [Category.id_comp]
    · change P.connecting ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 X) =
        e.hom ≫ (e.inv ≫ P.connecting)
      rw [Functor.map_id, Category.comp_id, e.hom_inv_id_assoc]
  rw [hmap, hmapInv]
  exact hdist

/-- The canonical presentation associated to `P.hasProduct` is distinguished when its explicit
difference is written as the legacy `milnorDifferenceMap`. -/
@[stacks 08TC]
theorem canonicalPresentation_mem_distTriang
    {K : SequentialInverseSystem D} {X : D} (P : Presentation K X) :
    letI := P.hasProduct
    Triangle.mk P.canonicalPresentation.ι K.milnorDifferenceMap
      P.canonicalPresentation.connecting ∈ distTriang D := by
  letI := P.hasProduct
  let Q := getLimitCone (Discrete.functor K.family)
  change Triangle.mk (P.ι ≫ SequentialInverseSystem.Milnor.ProductCone.map P.product Q (𝟙 K))
    K.milnorDifferenceMap
    (SequentialInverseSystem.Milnor.ProductCone.map Q P.product (𝟙 K) ≫ P.connecting) ∈
      distTriang D
  rw [← compatibility_difference_getLimitCone]
  exact compatibility_changeProduct_distinguished P Q

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
    P.toIsDerivedLimit.stageProjection n = P.stageProjection n := by
  change P.canonicalPresentation.stageProjection n = P.stageProjection n
  exact P.canonicalPresentation_stageProjection n

end HomotopyLimit.Presentation

namespace HomotopyLimit

/-- Stacks 08TC: existence of a legacy derived-limit witness is equivalent to the neutral
presentation-independent homotopy-limit predicate. -/
@[stacks 08TC]
theorem nonempty_isDerivedLimit_iff_isOf
    {K : SequentialInverseSystem D} {X : D} :
    Nonempty (IsDerivedLimit K X) ↔ HomotopyLimit.IsOf K X := by
  constructor
  · rintro ⟨h⟩
    exact h.toIsOf
  · rintro ⟨Q, ι, δ, hdist⟩
    let P : Presentation K X := ⟨Q, ι, δ, hdist⟩
    letI := P.hasProduct
    refine ⟨{ hasProduct := P.hasProduct, milnor :=
      { ι := P.ι ≫ SequentialInverseSystem.Milnor.ProductCone.map P.product
          (getLimitCone (Discrete.functor K.family)) (𝟙 K)
        δ := SequentialInverseSystem.Milnor.ProductCone.map
          (getLimitCone (Discrete.functor K.family)) P.product (𝟙 K) ≫ P.connecting
        mem_distTriang := by
          rw [← compatibility_difference_getLimitCone]
          exact Presentation.compatibility_changeProduct_distinguished P _ } }⟩

end HomotopyLimit

end CategoryTheory
