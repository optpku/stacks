/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Pseudofunctor.Equivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for fibred-category two-fibre products

This leaf specializes the generic locally induced projection strong transformations and exposes
their components and both directions of their naturality comparisons.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

/-- The canonical first projection from the two-fibre-product pseudofunctor of fibred
categories to the left-endpoint projection on bundled cospans. -/
@[stacks 02XQ "first projection transformation for two-fibre products of fibred categories"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor (C := C))
      (Bicategory.Cospan.leftProjection
        (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :=
  LocallyInduced.TwoFibreProduct.pseudofunctor.fst
    (BasedCategory.isFibered C) (FiberedCategoryOver.homProperty C)

/-- The canonical second projection from the two-fibre-product pseudofunctor of fibred
categories to the right-endpoint projection on bundled cospans. -/
@[stacks 02XQ "second projection transformation for two-fibre products of fibred categories"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor (C := C))
      (Bicategory.Cospan.rightProjection
        (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :=
  LocallyInduced.TwoFibreProduct.pseudofunctor.snd
    (BasedCategory.isFibered C) (FiberedCategoryOver.homProperty C)

/-- The component of the first-projection transformation is the application-facing first
projection. -/
@[simp]
theorem pseudofunctor.fst.app
    (S : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor.fst (C := C)).app S =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.fst S.fst S.snd := sorry

/-- Naturality of the first-projection transformation is heterogeneously equal to the
application-facing first-projection comparison. -/
theorem pseudofunctor.fst.naturality
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fst (C := C)).naturality ψ ≍
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The forward naturality cell of the first projection is the forward application-facing
comparison cell. -/
theorem pseudofunctor.fst.naturality.hom
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.fst (C := C)).naturality ψ).hom ≍
      (_root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).hom := sorry

/-- The inverse naturality cell of the first projection is the inverse application-facing
comparison cell. -/
theorem pseudofunctor.fst.naturality.inv
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.fst (C := C)).naturality ψ).inv ≍
      (_root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).inv := sorry

/-- The component of the second-projection transformation is the application-facing second
projection. -/
@[simp]
theorem pseudofunctor.snd.app
    (S : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)) :
    (pseudofunctor.snd (C := C)).app S =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.snd S.fst S.snd := sorry

/-- Naturality of the second-projection transformation is heterogeneously equal to the
application-facing second-projection comparison. -/
theorem pseudofunctor.snd.naturality
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.snd (C := C)).naturality ψ ≍
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The forward naturality cell of the second projection is the forward application-facing
comparison cell. -/
theorem pseudofunctor.snd.naturality.hom
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.snd (C := C)).naturality ψ).hom ≍
      (_root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).hom := sorry

/-- The inverse naturality cell of the second projection is the inverse application-facing
comparison cell. -/
theorem pseudofunctor.snd.naturality.inv
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (ψ : S ⟶ T) :
    ((pseudofunctor.snd (C := C)).naturality ψ).inv ≍
      (_root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).inv := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
