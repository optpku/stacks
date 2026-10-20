/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.SourceSquare
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Iso

/-!
# Product-slice source-square comparison

This leaf owns the direct comparison from the product-slice source square to
its explicit right-vertical model, together with projection-level computation
rules for the comparison isomorphisms.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

open Limits.CategoricalPullback.ProductSlice

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.ProductSlice

section ProductSliceSourceRightVertical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable [Limits.HasBinaryProducts C]
variable {U V : C}

/-- The right vertical associated to `sourceSquare`:
`C/(U × V) ⥤ X ×_C X`. -/
@[stacks 04SF "right vertical of the product-slice source square"]
noncomputable def sourceSquare.rightVertical
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Over (Limits.prod U V) ⥤ X.p ⊡ X.p :=
  RightVertical.functor
    (RightVertical.baseIso
      (FiberedCategoryOver.Groupoids.commIso G)
      (FiberedCategoryOver.Groupoids.commIso G'))

/-- The direct square-comparison target is the explicit product-slice right vertical. -/
theorem sourceSquare.comparisonTarget.eq
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    PseudoPullbackComparison.target (sourceSquare (X := X) G G') =
      sourceSquare.rightVertical (X := X) G G' := sorry
/- Proof strategy: unfold both functors and use
`baseIso.toFunctorIso`; their object and morphism fields then agree. -/

namespace sourceSquare.Implementation

/-- Compatibility of the identity leg isomorphisms comparing the direct square target with the
explicit product-slice right vertical. -/
private theorem comparisonTargetIsoApp_w
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    X.p.map (𝟙 _) ≫ (sourceSquare.rightVertical (X := X) G G' |>.obj a).iso.hom =
      (PseudoPullbackComparison.target (sourceSquare (X := X) G G') |>.obj a).iso.hom ≫
        X.p.map (𝟙 _) := sorry

/-- The objectwise direct-target comparison. Its two non-Prop leg components are identity
isomorphisms. -/
private noncomputable def comparisonTargetIsoApp
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (PseudoPullbackComparison.target (sourceSquare (X := X) G G')).obj a ≅
      (sourceSquare.rightVertical (X := X) G G').obj a :=
  CategoricalPullback.mkIso
    (Iso.refl _) (Iso.refl _)
    (comparisonTargetIsoApp_w X G G' a)

/-- The explicit direct-target comparisons are natural in product-slice morphisms. -/
private theorem comparisonTargetIsoApp_naturality
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    {a b : Over (Limits.prod U V)} (f : a ⟶ b) :
    (PseudoPullbackComparison.target (sourceSquare (X := X) G G')).map f ≫
        (comparisonTargetIsoApp X G G' b).hom =
      (comparisonTargetIsoApp X G G' a).hom ≫
        (sourceSquare.rightVertical (X := X) G G').map f := sorry

end sourceSquare.Implementation

/-- The direct square-comparison target identified with
`sourceSquare.rightVertical`. -/
@[stacks 04SF "product-slice comparison target identification"]
noncomputable def sourceSquare.comparisonTargetIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    PseudoPullbackComparison.target (sourceSquare (X := X) G G') ≅
      sourceSquare.rightVertical (X := X) G G' :=
  NatIso.ofComponents
    (sourceSquare.Implementation.comparisonTargetIsoApp X G G')
    (fun f ↦ sourceSquare.Implementation.comparisonTargetIsoApp_naturality X G G' f)

/-- The first component of the forward direct-target comparison is the identity. -/
@[simp]
theorem sourceSquare.comparisonTargetIso.hom.app.fst
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonTargetIso (X := X) G G').hom.app a).fst = 𝟙 _ := sorry

/-- The second component of the forward direct-target comparison is the identity. -/
@[simp]
theorem sourceSquare.comparisonTargetIso.hom.app.snd
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonTargetIso (X := X) G G').hom.app a).snd = 𝟙 _ := sorry

/-- The first component of the inverse direct-target comparison is the identity. -/
@[simp]
theorem sourceSquare.comparisonTargetIso.inv.app.fst
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonTargetIso (X := X) G G').inv.app a).fst = 𝟙 _ := sorry

/-- The second component of the inverse direct-target comparison is the identity. -/
@[simp]
theorem sourceSquare.comparisonTargetIso.inv.app.snd
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonTargetIso (X := X) G G').inv.app a).snd = 𝟙 _ := sorry

/-- The product-slice source-square comparison after the Remark-4.35.8 equivalence. -/
@[stacks 04SF "product-slice source-square comparison"]
noncomputable def sourceSquare.comparisonIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    PseudoPullbackComparison.map
        (PseudoPullbackCone.map (sourceSquare.coneComparison G G')) ≅
      sourceSquare.rightVertical (X := X) G G' :=
  PseudoPullbackComparison.iso (sourceSquare.coneComparison G G') ≪≫
    sourceSquare.comparisonTargetIso (X := X) G G'

/-- The first component of the forward source-square comparison is the corresponding component
of the universal pseudo-pullback comparison. -/
@[simp]
theorem sourceSquare.comparisonIso.hom.app.fst
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonIso (X := X) G G').hom.app a).fst =
      ((PseudoPullbackComparison.iso
        (sourceSquare.coneComparison G G')).hom.app a).fst := sorry

/-- The second component of the forward source-square comparison is the corresponding component
of the universal pseudo-pullback comparison. -/
@[simp]
theorem sourceSquare.comparisonIso.hom.app.snd
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonIso (X := X) G G').hom.app a).snd =
      ((PseudoPullbackComparison.iso
        (sourceSquare.coneComparison G G')).hom.app a).snd := sorry

/-- The first component of the inverse source-square comparison is the corresponding component
of the inverse universal pseudo-pullback comparison. -/
@[simp]
theorem sourceSquare.comparisonIso.inv.app.fst
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonIso (X := X) G G').inv.app a).fst =
      ((PseudoPullbackComparison.iso
        (sourceSquare.coneComparison G G')).inv.app a).fst := sorry

/-- The second component of the inverse source-square comparison is the corresponding component
of the inverse universal pseudo-pullback comparison. -/
@[simp]
theorem sourceSquare.comparisonIso.inv.app.snd
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    ((sourceSquare.comparisonIso (X := X) G G').inv.app a).snd =
      ((PseudoPullbackComparison.iso
        (sourceSquare.coneComparison G G')).inv.app a).snd := sorry

end ProductSliceSourceRightVertical

end FiberedCategoryOver.Groupoids.ProductSlice

end CategoryTheory
