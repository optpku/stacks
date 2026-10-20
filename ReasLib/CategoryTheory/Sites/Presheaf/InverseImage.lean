/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image on presheaves

Precomposition is the canonical inverse-image operation on presheaf categories.  This leaf owns
the functor and its exactness without importing simplicial or topology-specific constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v u' v' w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']

/-- The inverse-image functor on `A`-valued presheaves induced by `u : C' ⥤ C`. -/
@[stacks 08QA "presheaf inverse image by precomposition"]
abbrev presheafInverseImage (u : C' ⥤ C) (A : Type w) [Category A] :
    (Cᵒᵖ ⥤ A) ⥤ (C'ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ A).obj u.op

section Abelian

variable (A : Type w) [Category A] [Abelian A]

/-- Precomposition is additive on abelian-valued presheaves. -/
instance presheafInverseImage_additive (u : C' ⥤ C) :
    (presheafInverseImage u A).Additive := inferInstance

/-- Precomposition preserves finite limits on abelian-valued presheaves. -/
instance presheafInverseImage_preservesFiniteLimits (u : C' ⥤ C) :
    PreservesFiniteLimits (presheafInverseImage u A) := inferInstance

/-- Precomposition preserves finite colimits on abelian-valued presheaves. -/
instance presheafInverseImage_preservesFiniteColimits (u : C' ⥤ C) :
    PreservesFiniteColimits (presheafInverseImage u A) := inferInstance

/-- Precomposition, bundled as the canonical exact inverse-image functor on abelian-valued
presheaves. -/
@[stacks 08QA "exact presheaf inverse image"]
abbrev presheafInverseImageExact (u : C' ⥤ C) :
    (Cᵒᵖ ⥤ A) ⥤ₑ (C'ᵒᵖ ⥤ A) :=
  ExactFunctor.of (presheafInverseImage u A)

end Abelian

end CategoryTheory.Functor
