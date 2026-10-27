/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition

/-!
# Identity and composition of cartesian based functors

This module supplies the categorical operations on universe-polymorphic cartesian based functors
and their standard computation API on based functors, total functors, objects, morphisms, and
fibers.
-/

@[expose] public section

universe u v uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- The identity cartesian based functor. -/
def id (p : S₁ ⥤ C) : CartesianBasedFunctor p p where
  obj := BasedFunctor.id (BasedCategory.ofFunctor p)
  property := BasedFunctor.PreservesStronglyCartesian.id _

/-- The based functor underlying the identity cartesian based functor is the identity. -/
@[simp]
theorem id.toBasedFunctor (p : S₁ ⥤ C) :
    (id p).toBasedFunctor =
      BasedFunctor.id (BasedCategory.ofFunctor p) := rfl

/-- The total functor underlying the identity cartesian based functor is the identity. -/
@[simp]
theorem id.toFunctor (p : S₁ ⥤ C) :
    (id p).toFunctor = 𝟭 S₁ := rfl

/-- Composition of universe-polymorphic cartesian based functors. -/
def comp {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃) :
    CartesianBasedFunctor p₁ p₃ where
  obj := BasedFunctor.comp F.toBasedFunctor G.toBasedFunctor
  property :=
    BasedFunctor.PreservesStronglyCartesian.comp
      F.preservesStronglyCartesian G.preservesStronglyCartesian

/-- The based functor underlying a composite is the composite of the underlying based functors. -/
@[simp]
theorem comp.toBasedFunctor
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃) :
    (F.comp G).toBasedFunctor =
      BasedFunctor.comp F.toBasedFunctor G.toBasedFunctor := rfl

/-- The total functor underlying a composite is the composite of the total functors. -/
@[simp]
theorem comp.toFunctor
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃) :
    (F.comp G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

/-- The identity cartesian based functor acts identically on total-category objects. -/
@[simp]
theorem id.obj (p : S₁ ⥤ C) (x : S₁) :
    (id p).toFunctor.obj x = x := rfl

/-- The identity cartesian based functor acts identically on total-category morphisms. -/
@[simp]
theorem id.map (p : S₁ ⥤ C) {x y : S₁} (f : x ⟶ y) :
    (id p).toFunctor.map f = f := rfl

/-- Composition of cartesian based functors is computed by successive application on objects. -/
@[simp]
theorem comp.obj {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃) (x : S₁) :
    (F.comp G).toFunctor.obj x = G.toFunctor.obj (F.toFunctor.obj x) := rfl

/-- Composition of cartesian based functors is computed by successive application on
morphisms. -/
@[simp]
theorem comp.map {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    {x y : S₁} (f : x ⟶ y) :
    (F.comp G).toFunctor.map f =
      G.toFunctor.map (F.toFunctor.map f) := rfl

/-- The fiber functor induced by the identity cartesian based functor is the identity. -/
@[simp]
theorem fiberFunctor.id (p : S₁ ⥤ C) (U : C) :
    (id p).fiberFunctor U = 𝟭 (p.Fiber U) := rfl

/-- The fiber functor induced by a composite is the composite of the induced fiber functors. -/
@[simp]
theorem fiberFunctor.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃) (U : C) :
    (F.comp G).fiberFunctor U =
      F.fiberFunctor U ⋙ G.fiberFunctor U := rfl

end CartesianBasedFunctor

end CategoryTheory

/- Axiom audit: identity and composition store only their canonical underlying based functors;
any `sorryAx` is confined to Prop-valued preservation and computation fields. -/
