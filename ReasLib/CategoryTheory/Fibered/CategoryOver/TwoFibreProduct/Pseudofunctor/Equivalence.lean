/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences induced by fibred-category two-fibre products

This leaf exposes the apex-facing equivalence and its structural components. The generic
`Pseudofunctor.mapEquivalence` construction remains the data owner.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

/-- A bicategorical equivalence of bundled cospans induces the canonical equivalence of their
application-facing two-fibre-product apices. -/
@[stacks 02XQ "equivalence of two-fibre products of fibred categories"]
noncomputable def pseudofunctor.mapEquivalence
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (e : S ≌ T) :
    apex S.fst S.snd ≌ apex T.fst T.snd :=
  (pseudofunctor (C := C)).mapEquivalence e

/-- The forward morphism of the induced equivalence is the two-fibre-product map associated to
the forward bundled-cospan morphism. -/
@[simp]
theorem pseudofunctor.mapEquivalence.hom
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).hom =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.hom) := sorry

/-- The inverse morphism of the induced equivalence is the two-fibre-product map associated to
the inverse bundled-cospan morphism. -/
@[simp]
theorem pseudofunctor.mapEquivalence.inv
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).inv =
      _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.inv) := sorry

/-- The unit of the equivalence induced by a bundled-cospan equivalence is the canonical
pseudofunctorial unit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.unit
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor (C := C)) e := sorry

/-- The counit of the equivalence induced by a bundled-cospan equivalence is heterogeneously
equal to the canonical pseudofunctorial counit. -/
theorem pseudofunctor.mapEquivalence.counit
    {S T : Bicategory.Cospan
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).counit ≍
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor (C := C)) e := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
